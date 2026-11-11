-- Prove2me | Definitions.Def_Q226II019
-- name    : Q226II019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T18:10:27.758421+00:00
-- url     : https://prove2.me/theorems/c7d0f22f-e52b-4a78-a237-163e983ecf0e
-- title:
--   Definitions bundle Q226II019 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 2 definitions and 29 theorems. The definitions and types are `OAI.SmoothLocal.Geometry.counterexampleMetric`, `OAI.SmoothLocal.Geometry.selectedPatchTensor`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Assembly_FinalMetric`, `IsometricImmersion_Assembly_SelectedPatchObstructions`, `IsometricImmersion_Caps_ActualClassTwoSidedCauchy`, `IsometricImmersion_Caps_ActualOffPulseCauchy`, `IsometricImmersion_Caps_ActualUpperOffPulseCauchy`, `IsometricImmersion_Comparison_ActualClassComparisonGradient`, `IsometricImmersion_Comparison_ActualClassComparisonMoment`, `IsometricImmersion_Comparison_ActualClassComparisonSourceBound`, `IsometricImmersion_Comparison_ActualComparisonCoefficientData`, `IsometricImmersion_Comparison_ActualUniformComparisonGradient`, `IsometricImmersion_Comparison_ComparisonSourceBounds`, `IsometricImmersion_Comparison_OriginalClassComparisonWithLow`, `IsometricImmersion_Coordinates_ActualReferenceSegment`, `IsometricImmersion_Estimates_ActualQApplicability`, `IsometricImmersion_Estimates_ActualQMomentLower`, `IsometricImmersion_Estimates_ActualQMomentPositive`, `IsometricImmersion_Estimates_ActualQWeightedRemainder`, `IsometricImmersion_Obstructions_BoundedClassNowhereDense`, `IsometricImmersion_Obstructions_PatchResidualTheorem`, `IsometricImmersion_Obstructions_SmallPatchObstruction`, `IsometricImmersion_Pulses_ActualClassQForcingMoment`, `IsometricImmersion_Pulses_ActualQPulseForcingGlobal`, `IsometricImmersion_Pulses_OriginalPulseExclusion`, `IsometricImmersion_Taylor_ActualTaylorFiniteJets`, `IsometricImmersion_Taylor_ActualUniformTaylorPulse`, `IsometricImmersion_Taylor_ActualUniformTaylorRich`, `IsometricImmersion_Taylor_FiniteTaylorComparison`, `IsometricImmersion_Taylor_UniformTaylorPulse`, `IsometricImmersion_Taylor_UniformTaylorStrip`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II017` and `Q226II018` of this split.
--
--   **Imported by** (directly, in this split): the proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 334; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Encodable.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.Interval.Set.Pi
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Closure
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II017
import Definitions.Def_Q226II018

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ActualQPulseForcingGlobal
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise
namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_Q_pulse_forcing_bound_global (B Bcompare BQ D A : ℝ)
    {d dcompare c : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ H Cfirst Ctest Ccompare : ℝ,
      0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ p : Coord, inverseShearCoordinates q0 p ∈ U →
          ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
          let gs := metricInShearCoordinates gStar q0
          let gt := metricInShearCoordinates gTau q0
          let zs := heightInShearCoordinates z q0
          ∀ epsilon epsilonQ : ℝ,
            ‖actualCurvatureFirstInput gs p‖ ≤ B → d ≤ (gs p).det →
            ‖actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
              (inverseShearCoordinates q0 p)‖ ≤ Bcompare →
            dcompare ≤ (testMetric gStar q0 a N delta tau (inverseShearCoordinates q0 p)).det →
            ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
              actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
                (inverseShearCoordinates q0 p)‖ ≤ epsilon →
            epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            (∀ i j k l : Fin 2,
              |coordPartial i (coordPartial j (fun q => gTau q k l)) (inverseShearCoordinates q0 p)-
                coordPartial i (coordPartial j (fun q => testMetric gStar q0 a N delta tau q k l))
                  (inverseShearCoordinates q0 p)| ≤ epsilon) →
            ‖qFirstBundle gs (qSolutionJet zs p)‖ ≤ BQ →
            c ≤ |covHessian gs zs p 0 0| →
            ‖actualCurvatureFirstInput gt p-actualCurvatureFirstInput gs p‖ ≤ epsilonQ →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            |curvatureDensity gTau (inverseShearCoordinates q0 p)| ≤ D →
            |forcingCoefficient gs zs p| ≤ A →
            |(sixVariableQ gt (qSolutionJet zs p)-sixVariableQ gs (qSolutionJet zs p))-
                2*forcingCoefficient gs zs p*pulsePrincipalLeading a N delta tau p| ≤
              2*A*(testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+Ccompare*epsilon)+
                Cfirst*epsilonQ := by
  obtain ⟨H,Cfirst,hH,hCfirst,hQ⟩ := exists_actual_Q_forcing_error_bound BQ D A hD hA hd hc
  obtain ⟨Ctest,Ccompare,hCt,hCc,hDensity⟩ :=
    exists_actual_density_global_bound B Bcompare hd hdcompare ha N hN
  refine ⟨H,Cfirst,Ctest,Ccompare,hH,hCfirst,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hDensityT⟩ := hDensity delta hdelta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpU z hz
  dsimp only
  intro epsilon epsilonQ hB hdet hBcompare hdetcompare hdist he1 hsmall hsecond
    hBQ hxx hdistQ heQ1 hsmallQ hxxsmall hdensity hforce
  have hactualDensity := hDensityT tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpU
    hB hdet epsilon hBcompare hdetcompare hdist he1 hsmall hsecond
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hpV : p ∈ V := hpU
  have hgSV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgStar 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hgTV : SmoothPositiveOn (metricInShearCoordinates gTau q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgTau 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hdensityQ : |curvatureDensity (metricInShearCoordinates gTau q0) p| ≤ D := by
    rw [curvatureDensity_in_shear_coordinates hgTau hU q0 hpU]
    exact hdensity
  have hQactual := hQ (metricInShearCoordinates gTau q0) (metricInShearCoordinates gStar q0)
    V hgTV hgSV hV (heightInShearCoordinates z q0) p hpV epsilonQ
    (pulsePrincipalLeading a N delta tau p) hBQ hdet hxx hdistQ heQ1 hsmallQ hxxsmall
    hdensityQ hforce
  rw [curvatureDensity_in_shear_coordinates hgTau hU q0 hpU,
    curvatureDensity_in_shear_coordinates hgStar hU q0 hpU] at hQactual
  exact hQactual.trans (add_le_add
    (mul_le_mul_of_nonneg_left hactualDensity (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA)) le_rfl)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualQWeightedRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_Q_weighted_remainder_bound (B Bcompare BQ D A : ℝ)
    {d dcompare c : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ H Cfirst Ctest Ccompare : ℝ,
      0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
          ∀ epsilon epsilonQ : ℝ, 0 ≤ epsilon → 0 ≤ epsilonQ →
            epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            (∀ p ∈ pulseStrip a delta tau,
              QPulsePointBounds gStar gTau z U q0 a delta tau N
                B Bcompare BQ D A d dcompare c epsilon epsilonQ p) →
            |pulseWeightedMoment a delta tau (fun p => actualShearedQForcing gStar gTau z q0 p-
              actualShearedQLeading gStar z q0 a N delta tau p)| ≤
              qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ*
                (2*delta/tau)*(∫ x : ℝ, axisBump a x) := by
  obtain ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,hglobal⟩ :=
    exists_actual_Q_pulse_forcing_bound_global B Bcompare BQ D A hd hdcompare hc hD hA ha N hN
  refine ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hglobalT⟩ := hglobal delta hdelta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ he heQ
    he1 hesmall heQ1 heQsmall hxxsmall hpoint
  have htpos : 0 < tau := zero_lt_one.trans_le (hT.trans ht)
  apply pulseWeightedMoment_bound ha hdelta.le htpos
    (qForcingRemainderBudget_nonneg ha hA hCf hCt hCc N delta htpos.le he heQ)
  intro p hp
  have h := hpoint p hp
  exact hglobalT tau ht gStar gTau q0 U hgStar hgTest hgTau hU p h.point_mem z hz epsilon epsilonQ
    h.referenceFirst h.referenceDet h.testFirst h.testDet h.approximationFirst he1 hesmall
    h.approximationSecond h.referenceState h.referenceXX h.baseFirstDistance heQ1 heQsmall hxxsmall
    h.actualDensity h.referenceCoefficient

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualQMomentLower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_Q_moment_lower_with_remainder
    (B Bcompare BQ D A Dref Cref : ℝ) {d dcompare c e : ℝ}
    (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c) (he : 0 < e)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ c3 H Cfirst Ctest Ccompare : ℝ,
      0 < c3 ∧ 0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
          ∀ epsilon epsilonQ : ℝ, 0 ≤ epsilon → 0 ≤ epsilonQ →
            epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            (∀ p ∈ pulseStrip a delta tau,
              QPulsePointBounds gStar gTau z U q0 a delta tau N
                B Bcompare BQ D A d dcompare c epsilon epsilonQ p) →
            (∀ p ∈ pulseStrip a delta tau,
              covHessian (metricInShearCoordinates gTau q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0) →
            (∀ p ∈ pulseStrip a delta tau,
              e ≤ heightEnergy (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p) →
            (∀ p ∈ pulseStrip a delta tau, (metricInShearCoordinates gStar q0 p).det ≤ Dref) →
            (∀ p ∈ pulseStrip a delta tau,
              |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0| ≤ Cref) →
            c3*delta*tau/tau^N-
                qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ*
                  (2*delta/tau)*(∫ x : ℝ, axisBump a x) ≤
              |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| := by
  obtain ⟨c3,hc3,hLead⟩ := exists_actual_leading_forcing_moment_lower ha he hc Dref Cref N
  obtain ⟨Tlead,hTlead⟩ := eventually_atTop.mp hLead
  obtain ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,hError⟩ :=
    exists_actual_Q_weighted_remainder_bound B Bcompare BQ D A hd hdcompare hc hD hA ha N hN
  refine ⟨c3,H,Cfirst,Ctest,Ccompare,hc3,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨Terror,hTerror,hErrorT⟩ := hError delta hdelta
  refine ⟨max Terror Tlead,hTerror.trans (le_max_left _ _),?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ heps hepsQ
    heps1 hesmall hepsQ1 hepsQsmall hxxsmall hpoint hxxTau hE hdetup hxxup
  have htE : Terror ≤ tau := (le_max_left _ _).trans ht
  have htL : Tlead ≤ tau := (le_max_right _ _).trans ht
  have hSU : ∀ p ∈ pulseStrip a delta tau, inverseShearCoordinates q0 p ∈ U :=
    fun p hp => (hpoint p hp).point_mem
  have hxxStar : ∀ p ∈ pulseStrip a delta tau,
      covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
    intro p hp hz0
    have hm := (hpoint p hp).referenceXX
    rw [hz0,abs_zero] at hm
    linarith
  have hFc : ContinuousOn (actualShearedQForcing gStar gTau z q0) (pulseStrip a delta tau) :=
    ((sheared_Q_on_height_contDiffOn hgTau hz hU q0 hSU hxxTau).sub
      (sheared_Q_on_height_contDiffOn hgStar hz hU q0 hSU hxxStar)).continuousOn
  have hLc := (actualShearedQLeading_contDiffOn hgStar hz hU q0 a N delta tau hSU hxxStar).continuousOn
  have herr := hErrorT tau htE gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ
    heps hepsQ heps1 hesmall hepsQ1 hepsQsmall hxxsmall hpoint
  rw [pulseWeightedMoment_sub hFc hLc] at herr
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hgStar 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hzV : ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) V :=
    heightInShearCoordinates_contDiffOn hz q0
  have hSV : pulseStrip a delta tau ⊆ V := fun p hp => hSU p hp
  have hlead := hTlead tau htL delta hdelta (metricInShearCoordinates gStar q0)
    (heightInShearCoordinates z q0) V hgV hzV hV hSV hE hdetup
    (fun p hp => (hpoint p hp).referenceXX) hxxup
  change c3*delta*tau/tau^N ≤ |pulseWeightedMoment a delta tau
    (actualShearedQLeading gStar z q0 a N delta tau)| at hlead
  have htriangle : |pulseWeightedMoment a delta tau (actualShearedQLeading gStar z q0 a N delta tau)| ≤
      |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)|+
      |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)-
        pulseWeightedMoment a delta tau (actualShearedQLeading gStar z q0 a N delta tau)| := by
    calc
      _ = |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)-
        (pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)-
          pulseWeightedMoment a delta tau (actualShearedQLeading gStar z q0 a N delta tau))| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  linarith

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualQMomentPositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise
namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_Q_moment_positive_lower
    (B Bcompare BQ D A Dref Cref : ℝ) {d dcompare c e : ℝ}
    (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c) (he : 0 < e)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ c3 H Cfirst Ctest Ccompare : ℝ,
      0 < c3 ∧ 0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
          ∀ epsilon epsilonQ : ℝ, 0 ≤ epsilon → 0 ≤ epsilonQ →
            epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            epsilon ≤ tau/tau^N → epsilonQ ≤ qPulseFirstJetBudget a ha N delta tau →
            (∀ p ∈ pulseStrip a delta tau,
              QPulsePointBounds gStar gTau z U q0 a delta tau N
                B Bcompare BQ D A d dcompare c epsilon epsilonQ p) →
            (∀ p ∈ pulseStrip a delta tau,
              covHessian (metricInShearCoordinates gTau q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0) →
            (∀ p ∈ pulseStrip a delta tau,
              e ≤ heightEnergy (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p) →
            (∀ p ∈ pulseStrip a delta tau, (metricInShearCoordinates gStar q0 p).det ≤ Dref) →
            (∀ p ∈ pulseStrip a delta tau,
              |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0| ≤ Cref) →
            c3*delta*tau/tau^N ≤
              |pulseWeightedMoment a delta tau (actualShearedQForcing gStar gTau z q0)| := by
  obtain ⟨c3,H,Cfirst,Ctest,Ccompare,hc3,hH,hCf,hCt,hCc,hbase⟩ :=
    exists_actual_Q_moment_lower_with_remainder B Bcompare BQ D A Dref Cref
      hd hdcompare hc he hD hA ha N hN
  refine ⟨c3/2,H,Cfirst,Ctest,Ccompare,half_pos hc3,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨Tbase,hTbase,hbaseT⟩ := hbase delta hdelta
  obtain ⟨Tabs,_,habs⟩ := qMoment_budget_absorption_threshold ha hc3 hA hCf hCt hCc N delta hdelta.le
  refine ⟨max Tbase Tabs,hTbase.trans (le_max_left _ _),?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z hz epsilon epsilonQ heps hepsQ
    heps1 hesmall hepsQ1 hepsQsmall hxxsmall heScale heQScale hpoint hxxTau hE hdetup hxxup
  have hbase' := hbaseT tau ((le_max_left _ _).trans ht) gStar gTau q0 U hgStar hgTest hgTau hU z hz
    epsilon epsilonQ heps hepsQ heps1 hesmall hepsQ1 hepsQsmall hxxsmall hpoint hxxTau hE hdetup hxxup
  have habs' := habs tau ((le_max_right _ _).trans ht) epsilon epsilonQ heScale heQScale
  have hhalf : (c3/2)*delta*tau/tau^N = (c3*delta*tau/tau^N)/2 := by ring
  rw [hhalf] at habs' ⊢
  linarith

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_FiniteTaylorComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem finiteTaylorComparison {g : MetricField} {U : Set Coord}
    {u0 u1 : ℝ → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0) (N : ℕ) :
    let z0 := taylorApproximation g a u0 u1 N
    ContDiffOn ℝ ∞ z0 (spatialStrip I) ∧
    (∀ x ∈ I, z0 ![x, a] = u0 x ∧ coordPartial 1 z0 ![x, a] = u1 x) ∧
    (∀ x, ∃ p : Polynomial ℝ, p.natDegree ≤ N + 1 ∧
      ∀ t, p.eval t = z0 ![x, t]) ∧
    (∃ V : Set Coord, IsOpen V ∧ V ⊆ U ∩ spatialStrip I ∧
      (∀ x ∈ I, (![x, a] : Coord) ∈ V) ∧
      (∀ p ∈ V, covHessian g z0 p 0 0 ≠ 0) ∧
      ContDiffOn ℝ ∞ (qResidual g z0) V) ∧
    (∀ x ∈ I, ∀ k < N, iteratedDeriv k (fun t => qResidual g z0 ![x, t]) a = 0) := by
  dsimp only
  obtain ⟨hP, hjet, hzero⟩ := taylorApproximation_properties hg hU hI h0 h1 a hcut hxx N
  have hxxN : ∀ x ∈ I,
      covHessian g (taylorApproximation g a u0 u1 N) ![x, a] 0 0 ≠ 0 := by
    intro x hx
    rw [← stateQDenominator_qSolutionJet, hjet x hx, stateQDenominator_qSolutionJet]
    exact hxx x hx
  refine ⟨hP, ?_, ?_, ?_, hzero⟩
  · intro x hx
    refine ⟨taylorApproximation_value g a x u0 u1 N, ?_⟩
    have hv := congrArg (fun w : DarbouxState => w 3) (hjet x hx)
    change coordPartial 1 (taylorApproximation g a u0 u1 N) ![x, a] =
      coordPartial 1 (linearCauchy a u0 u1) ![x, a] at hv
    exact hv.trans (linearCauchy_velocity hI h0 h1 a hx)
  · intro x
    exact ⟨comparisonTimePolynomial g a u0 u1 x N,
      comparisonTimePolynomial_natDegree g a u0 u1 x N,
      fun t => comparisonTimePolynomial_eval g a u0 u1 x t N⟩
  · refine ⟨comparisonDomain g U (taylorApproximation g a u0 u1 N) I,
      comparisonDomain_isOpen hg hU hI hP, ?_, ?_, ?_, qResidual_contDiffOn hg hU hI hP⟩
    · intro p hp
      exact ⟨(comparisonDomain_denominator hp).1, hp.1⟩
    · intro x hx
      exact mem_comparisonDomain hx (hcut x hx) (hxxN x hx)
    · intro p hp
      exact (comparisonDomain_denominator hp).2

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ActualTaylorFiniteJets
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_taylor_finite_jets_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
          ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
            (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
            CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
            CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
            (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            let zs := heightInShearCoordinates z q0
            let gs := metricInShearCoordinates gStar q0
            let P := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ j ≤ K, ∀ p : Coord, |p 0| ≤ boundedClassWidth kappa M*r/2 →
              |p 1| ≤ delta/(tau : ℝ) → ‖iteratedFDeriv ℝ j P p‖ ≤ C) ∧
            CoordinateBound P (pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ)) K C := by
  let L := boundedClassWidth kappa M
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let S := shearedModelSquare q0
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hgs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  have hS : IsCompact S := shearedModelSquare_isCompact q0
  have hSVs : S ⊆ Vs := shearedModelSquare_subset_domain hSV q0
  obtain ⟨tauRef,htauRef,hfloor⟩ := exists_bounded_patch_reference_initial_floor
    G kappa d q0 M hG hkappa hd hM hq0
  obtain ⟨B,hB,hCauchyK⟩ := exists_actual_off_pulse_cauchy_bounds_at_radius
    hgStar hV hSV M hG hd hkappa hM hq0 hr hrhalf hLr hrsmall (taylorInitialRequest N K)
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hc : 0 < c := div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  obtain ⟨C,hC,hpoly⟩ := uniform_taylorApproximation_jets hgs hVs hS hSVs
    (initialShearedStateBudget (M : ℝ) q0) (initialShearedStateBudget_nonneg _ _) hc B hB N K
  refine ⟨C,hC,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hCauchyK N delta hdelt,hwidth,eventually_ge_atTop tauRef] with tau hCauchyTau hwidthTau htauR
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let a := -delta/(tau : ℝ)
  let zs := heightInShearCoordinates z q0
  let I := Ioo (-(L*r)) (L*r)
  let J := Icc (-(L*r/2)) (L*r/2)
  have htau1 : 1 ≤ tau := htauRef.trans htauR
  have htauPos : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau1)
  have hdw : delta/(tau : ℝ) ≤ r := by
    have he : delta/(tau : ℝ) = 2*(delta/(2*(tau : ℝ))) := by ring
    rw [he]
    linarith [hwidthTau.2]
  have habs : |a| ≤ r := by
    dsimp only [a]
    rw [abs_div,abs_neg,abs_of_pos hdelt,abs_of_pos htauPos]
    exact hdw
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hcutS (x : ℝ) (hx : x ∈ I) : inverseShearCoordinates q0 ![x,a] ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨abs_le.mpr ⟨hx.1.le,hx.2.le⟩,habs⟩
  have hcutU (x : ℝ) (hx : x ∈ I) : (![x,a] : Coord) ∈ inverseShearCoordinates q0 ⁻¹' U :=
    hSU (hcutS x hx)
  have hzs : ContDiffOn ℝ ∞ zs (inverseShearCoordinates q0 ⁻¹' U) :=
    heightInShearCoordinates_contDiffOn hh.smooth q0
  have hUs := shearedModelDomain_isOpen hU q0
  have hI : IsOpen I := isOpen_Ioo
  have hJI : J ⊆ I := by
    intro x hx
    exact ⟨by linarith [hx.1,mul_pos hL hr],by linarith [hx.2,mul_pos hL hr]⟩
  have hstate (x : ℝ) (hx : x ∈ I) :
      ‖qSolutionJet (linearCauchy a (heightCauchyValue zs a) (heightCauchyVelocity zs a)) ![x,a]‖ ≤
        initialShearedStateBudget (M : ℝ) q0 := by
    apply actual_initial_sheared_state_bound hh.smooth hU hSU (Nat.cast_nonneg M) hh.lowJet
      q0 (-(L*r)) (L*r) a hcutS hx
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · change ‖x‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact (abs_le.mpr ⟨hx.1.le,hx.2.le⟩).trans (hLr.trans (by norm_num))
    · change ‖a‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact habs.trans (by linarith)
  have hden := hfloor g0 gStar V eta z r N delta tau hgStar hV hSV hclass hr hLr hrsmall
    hgB hdet hcenter hdelt htauR hdw happ
  have hBactual := hCauchyTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have h0 := heightCauchyValue_contDiffOn hzs a hcutU
  have h1 := heightCauchyVelocity_contDiffOn hzs hUs a hcutU
  let P := taylorApproximation gs a (heightCauchyValue zs a) (heightCauchyVelocity zs a) N
  have hxx : ∀ x ∈ I, covHessian gs
      (linearCauchy a (heightCauchyValue zs a) (heightCauchyVelocity zs a)) ![x,a] 0 0 ≠ 0 := by
    intro x hx hzero
    have hl := hden x hx
    rw [hzero,abs_zero] at hl
    linarith
  have hP : ContDiffOn ℝ ∞ P (spatialStrip I) :=
    (taylorApproximation_properties hgs hVs hI h0 h1 a
      (fun x hx => hSVs (hcutS x hx)) hxx N).1
  have hb := hpoly (heightCauchyValue zs a) (heightCauchyVelocity zs a) I J a hI hJI h0 h1
    (fun x hx => hcutS x hx) hstate hden
    (fun x hx k hk => (hBactual x (abs_le.mpr hx) k hk).1)
    (fun x hx k hk => (hBactual x (abs_le.mpr hx) k hk).2)
  have hfull (j : ℕ) (hj : j ≤ K) (p : Coord) (hx : |p 0| ≤ L*r/2)
      (ht : |p 1| ≤ delta/(tau : ℝ)) : ‖iteratedFDeriv ℝ j P p‖ ≤ C := by
    apply hb j hj p (abs_le.mp hx)
    have hdelta : delta/(tau : ℝ) ≤ 1/2 :=
      (div_le_self hdelt.le hwidthTau.1).trans hdhalf
    have hpa : |p 1-a| ≤ |p 1|+|a| := by
      simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (p 1) 0 a
    have haeq : |a| = delta/(tau : ℝ) := by
      dsimp [a]
      rw [abs_div,abs_neg,abs_of_pos hdelt,abs_of_pos htauPos]
    rw [haeq] at hpa
    linarith
  refine ⟨hP,hfull,?_⟩
  apply coordinateBound_of_frechet_bounds hP (spatialStrip_isOpen hI)
  · intro p hp
    exact hJI hp.1
  · intro j hj p hp
    apply hfull j hj p (abs_le.mpr hp.1)
    simpa only [neg_div] using (abs_le.mpr hp.2)

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ActualReferenceSegment
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_reference_segment_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N : ℕ) (hN : 2 < N) :
    ∃ C A : ℝ, 0 ≤ C ∧ 1 ≤ A ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
          (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          let zs := heightInShearCoordinates z q0
          let gs := metricInShearCoordinates gStar q0
          let P := taylorApproximation gs (-delta/(tau : ℝ))
            (heightCauchyValue zs (-delta/(tau : ℝ)))
            (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
          ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
          CoordinateBound P (pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ)) 3 C ∧
          (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            ∀ sigma ∈ Icc (0 : ℝ) 1,
              (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) ≤
                |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ∧
              |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ≤ A ∧
              (1/(M : ℝ))/2 ≤ stateEnergy gs (qHeightJetSegment P zs sigma p) ∧
              ((((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))*(1/(M : ℝ)))/2)/A^2 ≤
                qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p) ∧
              (((kappa/2)/2)*((1/(M : ℝ))/2))/A^2 ≤
                (qFirstCoefficient gs 4 (qHeightJetSegment P zs sigma p)/2)^2+
                  qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p)) := by
  let L := boundedClassWidth kappa M
  let Z := (2*(1+|q0|))^3*(M : ℝ)
  let nu := (boundedClassSpeed kappa M)^2/(2*(M : ℝ))
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hnu : 0 < nu := boundedClassShearHxxFloor_pos hkappa hM
  have hZ : 0 ≤ Z := by dsimp only [Z] <;> positivity
  have hminv : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hq1 : |q0| ≤ 1 := hq0.trans (by norm_num)
  have ha : 0 < L*r/16 := div_pos (mul_pos hL hr) (by norm_num)
  obtain ⟨C,hC,hPjets⟩ := exists_actual_taylor_finite_jets_at_radius
    hgStar hV hSV M hG hd hkappa hM hq0 hr hrhalf hLr hrsmall N 3
  obtain ⟨epsilon,A,hepsilon,hA,htransfer⟩ := exists_uniform_Q_closed_strip_margins
    (16*G) 1 Z C (mul_nonneg (by norm_num) hG) (by norm_num) hZ hC
      hd hnu hminv hminv (half_pos hkappa)
  obtain ⟨tauRef,htauRef,hfloor⟩ := exists_bounded_patch_reference_initial_floor
    G kappa d q0 M hG hkappa hd hM hq0
  refine ⟨C,A,hC,hA,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  have hlarge : ∀ᶠ tau : ℕ in atTop, 2*delta*(Z+C)/epsilon ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hPjets delta hdelt hdhalf,hwidth,hlarge,eventually_ge_atTop tauRef,
    actual_sheared_metric_finite_reference_closeness hgStar hV hSV hq1 ha 2 N hN hepsilon delta]
    with tau hPtau hw htlarge htRef hclose
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates gStar q0
  let gt := metricInShearCoordinates g q0
  let zs := heightInShearCoordinates z q0
  let a := -delta/(tau : ℝ)
  let b := delta/(tau : ℝ)
  let I := Ioo (-(L*r)) (L*r)
  let P := taylorApproximation gs a (heightCauchyValue zs a) (heightCauchyVelocity zs a) N
  let S := closedRectangle (-(L*r/2)) (L*r/2) a b
  have hSP : S = pulseStrip (L*r/2) delta (tau : ℝ) := by
    simp only [S,pulseStrip,a,b,neg_div]
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let D := (Us ∩ Vs) ∩ spatialStrip I
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  have hD : IsOpen D := (hUs.inter hVs).inter (spatialStrip_isOpen isOpen_Ioo)
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le hw.1
  have hbnonneg : 0 ≤ b := div_nonneg hdelt.le htpos.le
  have hab : a ≤ b := by
    dsimp only [a,b]
    rw [neg_div]
    exact neg_le_self hbnonneg
  have hbr : b ≤ r := by
    have he : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    dsimp only [b]
    rw [he]
    linarith [hw.2]
  have haabs : |a| ≤ r := by
    dsimp only [a]
    rw [abs_div,abs_neg,abs_of_pos hdelt,abs_of_pos htpos]
    exact hbr
  have hLrpos : 0 < L*r := mul_pos hL hr
  have hhr : r ≤ 1/20 := by
    have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)
    have hh : r ≤ L*r := by nlinarith
    exact hh.trans hLr
  have hcoordinates (p : Coord) (hp : p ∈ S) : |p 0| ≤ L*r ∧ |p 1| ≤ r := by
    have hx : |p 0| ≤ L*r/2 := abs_le.mpr hp.1
    have ht : |p 1| ≤ b := abs_le.mpr
      ⟨by simpa only [a,b,neg_div] using hp.2.1,hp.2.2⟩
    exact ⟨hx.trans (by linarith),ht.trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ S) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hbox : S ⊆ D := by
    intro p hp
    refine ⟨⟨hSU (hpS p hp),hSV (hpS p hp)⟩,?_⟩
    exact ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩
  have hpoint (p : Coord) (hp : p ∈ S) : ‖p‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · exact (hcoordinates p hp).1.trans (hLr.trans (by norm_num))
    · exact (hcoordinates p hp).2.trans (hhr.trans (by norm_num))
  have hgtUs : SmoothPositiveOn gt Us := metricInShearCoordinates_smoothPositive hg q0
  have hgsVs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hgtD : SmoothPositiveOn gt D :=
    ⟨fun i j => (hgtUs.1 i j).mono (fun _ hp => hp.1.1),fun p hp => hgtUs.2 p hp.1.1⟩
  have hgsD : SmoothPositiveOn gs D :=
    ⟨fun i j => (hgsVs.1 i j).mono (fun _ hp => hp.1.2),fun p hp => hgsVs.2 p hp.1.2⟩
  have hzsUs : ContDiffOn ℝ ∞ zs Us := heightInShearCoordinates_contDiffOn hh.smooth q0
  have hzsD := hzsUs.mono (show D ⊆ Us from fun _ hp => hp.1.1)
  obtain ⟨hP,_hPfull,hPBpulse⟩ := hPtau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hPB : CoordinateBound P S 3 C := by rw [hSP]; exact hPBpulse
  have hPD : ContDiffOn ℝ ∞ P D := hP.mono inter_subset_right
  have hzB : CoordinateBound zs S 3 Z := bounded_class_sheared_C3_on_actual_region hclass q0 hpS
  have htwo (g1 : MetricField) (U1 : Set Coord) (hg1 : SmoothPositiveOn g1 U1)
      (hU1 : IsOpen U1) (hSU1 : modelSquare ⊆ U1)
      (hB1 : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => g1 q i j) p‖ ≤ G)
      (i j : Fin 2) (k : ℕ) (hk : k ≤ 2) (p : Coord) (hp : p ∈ S) :
      ‖iteratedFDeriv ℝ k (fun q => metricInShearCoordinates g1 q0 q i j) p‖ ≤ 16*G := by
    apply (sheared_metric_full_jet_bound hg1.1 hU1 hq1 hG (hSU1 (hpS p hp)) k
      (fun l m => hB1 l m k hk _ (hpS p hp)) i j).trans
    have he : (2 : ℝ)^k ≤ 4 := by
      exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk).trans (by norm_num)
    nlinarith
  have hg2 := htwo g U hg hU hSU (fun i j k hk => hgB i j k (by omega))
  have hgs2 := htwo gStar V hgStar hV hSV hgStarB
  have hdetT (p : Coord) (hp : p ∈ S) : d ≤ |(gt p).det| := by
    rw [metricDet_in_shear_coordinates]
    exact hdet _ (hpS p hp)
  have hdetR (p : Coord) (hp : p ∈ S) : d ≤ |(gs p).det| := by
    rw [metricDet_in_shear_coordinates]
    exact (hdStar _ (hpS p hp)).trans (le_abs_self _)
  have hmetric (i j : Fin 2) (k : ℕ) (hk : k ≤ 2) (p : Coord) (hp : p ∈ S) :
      ‖iteratedFDeriv ℝ k (fun q => gs q i j-gt q i j) p‖ ≤ epsilon :=
    hclose.2.2 g U hg hU hSU happ i j k hk p (hpS p hp)
  have hduration : (Z+C)*(b-a) ≤ epsilon := by
    have hh := (div_le_iff₀ hepsilon).mp htlarge
    have he : (Z+C)*(b-a)=(2*delta*(Z+C))/(tau : ℝ) := by dsimp only [a,b] <;> ring
    rw [he]
    apply (div_le_iff₀ htpos).mpr
    nlinarith
  have hcutS (x : ℝ) (hx : x ∈ I) : inverseShearCoordinates q0 ![x,a] ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨abs_le.mpr ⟨hx.1.le,hx.2.le⟩,haabs⟩
  have hcutU (x : ℝ) (hx : x ∈ I) : (![x,a] : Coord) ∈ Us := hSU (hcutS x hx)
  have h0 := heightCauchyValue_contDiffOn hzsUs a hcutU
  have h1 := heightCauchyVelocity_contDiffOn hzsUs hUs a hcutU
  have hden := hfloor g0 gStar V eta z r N delta tau hgStar hV hSV hclass hr hLr hrsmall
    hgB hdet hcenter hdelt htRef hbr happ
  have hxx0 : ∀ x ∈ I, covHessian gs (linearCauchy a (heightCauchyValue zs a)
      (heightCauchyVelocity zs a)) ![x,a] 0 0 ≠ 0 := by
    intro x hx hzero
    have hh := hden x hx
    rw [hzero,abs_zero] at hh
    have hc : 0 < (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) := by
      have he : (boundedClassSpeed kappa M)^2/(4*(M : ℝ))=nu/2 := by dsimp only [nu] <;> ring
      rw [he]
      exact half_pos hnu
    linarith
  have hjet0 := (taylorApproximation_properties hgsVs hVs isOpen_Ioo h0 h1 a
    (fun x hx => hSV (hcutS x hx)) hxx0 N).2.1
  have hinitial (x : ℝ) (hx : x ∈ Icc (-(L*r/2)) (L*r/2)) :
      qSolutionJet P (boxPoint x a)=qSolutionJet zs (boxPoint x a) := by
    have hxI : x ∈ I := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have he : boxPoint x a = (![x,a] : Coord) := by
      ext i
      fin_cases i <;> simp [boxPoint]
    rw [he]
    exact (hjet0 x hxI).trans (linearCauchy_height_initial_state hzsUs hUs (-(L*r)) (L*r) a hcutU hxI)
  have hresult := htransfer gt gs zs P D hgtD hgsD hD hzsD hPD
    (-(L*r/2)) (L*r/2) a b hab hbox hpoint hg2 hgs2 hzB hPB hdetT hdetR hmetric hduration hinitial
    (fun p hp => (hgeom p hp).2.1) (fun p hp => (hgeom p hp).2.2.1)
    (fun p hp => (hgeom p hp).2.2.2.1) (fun p hp => (hgeom p hp).2.2.2.2.1)
    (fun p hp => (hgeom p hp).2.2.2.2.2.1) (fun p hp => (hgeom p hp).2.2.2.2.2.2)
  refine ⟨hP,hPBpulse,?_⟩
  intro p hp sigma hsigma
  have hpS' : p ∈ S := by rw [hSP]; exact hp
  have hm := (hresult (p 0) hpS'.1 (p 1) hpS'.2).1 sigma hsigma
  have he : boxPoint (p 0) (p 1)=p := by ext i; fin_cases i <;> simp [boxPoint]
  have hhalf : nu/2=(boundedClassSpeed kappa M)^2/(4*(M : ℝ)) := by dsimp only [nu] <;> ring
  simpa only [he,hhalf] using hm

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonCoefficientData
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_comparison_coefficient_data_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N : ℕ) (hN : 2 < N) :
    ∃ K K1 : ℝ, 1 ≤ K ∧ 0 ≤ K1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
          (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          let zs := heightInShearCoordinates z q0
          let gs := metricInShearCoordinates gStar q0
          let P := taylorApproximation gs (-delta/(tau : ℝ))
            (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
          ∀ i : Fin 6, ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            |comparisonCoefficient gs P zs i p| ≤ K ∧
            |coordPartial 0 (comparisonCoefficient gs P zs i) p| ≤ K1 := by
  let L := boundedClassWidth kappa M
  let Z := (2*(1+|q0|))^3*(M : ℝ)
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hc : 0 < c := div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  obtain ⟨CP,_,_,_,hsegment⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  have hgs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  obtain ⟨K,hK,hcoeff⟩ := exists_uniform_comparison_coefficient_bounds hgs hVs
    (shearedModelSquare_isCompact q0) (shearedModelSquare_subset_domain hSV q0) 1 CP Z (by norm_num) hc
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  refine ⟨K,K*(max 1 CP+max 1 Z),hK,by positivity,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hsegment delta hdelt hdhalf,hwidth] with tau hsegmentTau hw
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let zs := heightInShearCoordinates z q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  let I := Ioo (-(L*r)) (L*r)
  let T := pulseStrip (L*r/2) delta (tau : ℝ)
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let D := (Us ∩ Vs) ∩ spatialStrip I
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hD : IsOpen D := (hUs.inter hVs).inter (spatialStrip_isOpen isOpen_Ioo)
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hcoordinates (p : Coord) (hp : p ∈ T) : |p 0| ≤ L*r ∧ |p 1| ≤ r :=
    ⟨(abs_le.mpr hp.1).trans (by linarith [mul_pos hL hr]),(abs_le.mpr hp.2).trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ T) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ T) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hTD : T ⊆ D := by
    intro p hp
    exact ⟨⟨hSU (hpS p hp),hSV (hpS p hp)⟩,
      ⟨by linarith [hp.1.1,mul_pos hL hr],by linarith [hp.1.2,mul_pos hL hr]⟩⟩
  have hpoint (p : Coord) (hp : p ∈ T) : ‖p‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · exact (hcoordinates p hp).1.trans (hLr.trans (by norm_num))
    · exact (hcoordinates p hp).2.trans (hrhalf.le.trans (by norm_num))
  have ht := hsegmentTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hP : ContDiffOn ℝ ∞ P D := ht.1.mono inter_subset_right
  have hzs : ContDiffOn ℝ ∞ zs D := (heightInShearCoordinates_contDiffOn hh.smooth q0).mono
    (fun _ hp => hp.1.1)
  have hzB : CoordinateBound zs T 3 Z := bounded_class_sheared_C3_on_actual_region hclass q0 hpS
  have hactual := hcoeff P zs D T hD (fun _ hp => hp.1.2) hP hzs
    (fun p hp => hpS p hp) hTD hpoint ht.2.1 hzB (fun p hp sigma hs => (ht.2.2 p hp sigma hs).1)
  dsimp only
  intro i p hp
  exact ⟨(hactual i p hp).1,(hactual i p hp).2 0⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_ActualUpperOffPulseCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.Flow.Reflection SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Taylor
open SmoothLocal.Model

theorem exists_actual_upper_off_pulse_cauchy_bounds_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (K : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U : Set Coord) (z : Coord → ℝ),
          SmoothPositiveOn g0 U → SmoothPositiveOn (perturbedMetric g0 eta.val) U →
          IsOpen U → modelSquare ⊆ U →
          (∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p) →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 8 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
            ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
              (delta/(tau : ℝ))) x‖ ≤ B ∧
            ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
              (delta/(tau : ℝ))) x‖ ≤ B := by
  have hqneg : |-q0| ≤ (1 : ℝ)/20 := by simpa only [abs_neg] using hq0
  obtain ⟨B,hB,hcauchy⟩ := exists_actual_off_pulse_cauchy_bounds_at_radius
    (q0 := -q0) (reflectedMetric_smoothPositive hgStar) (reflectedDomain_isOpen hV)
    (reflectedDomain_contains_modelSquare hSV) M hG hd hkappa hM hqneg hr hrhalf hLr hrsmall K
  refine ⟨B,hB,?_⟩
  intro N delta hdelt
  filter_upwards [hcauchy N delta hdelt] with tau hcauchyTau
  intro g0 eta U z hg0 hg hU hSU hbackground hh hclass hgB hdet hcenter happ x hx n hn
  let g := perturbedMetric g0 eta.val
  let gr := reflectedMetric g
  let zr := reflectedScalar z
  let UR := reflectPoint ⁻¹' U
  let etaR : metricPatchSet gr kappa := ⟨0,reflected_actual_metric_zero_patch eta hclass⟩
  have heR : perturbedMetric gr etaR.val = gr := perturbedMetric_zero gr
  have hgR : SmoothPositiveOn gr UR := reflectedMetric_smoothPositive hg
  have hhR : CapInductionHeight gr UR (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) zr :=
    reflected_capInductionHeight hg hU hSU hh
  have hcR : BoundedAdmissibleHeight gr M zr := hclass.reflected
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  obtain ⟨WR,YR,hfR⟩ := exists_actual_reflected_capInductionFlow eta hg0 hg hU hSU
    hG (Nat.cast_nonneg M) hd (one_div_pos.mpr hMR) (one_div_pos.mpr hMR)
    hgB hdet hh hkappa hbackground
  have hg4R : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => gr a i j) p‖ ≤ G := by
    intro i j k hk p hp
    change ‖iteratedFDeriv ℝ k (fun a => reflectedMetric g a i j) p‖ ≤ G
    rw [reflectedMetric_entry_jet_norm]
    exact hgB i j k (by omega) _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hdetR : ∀ p ∈ modelSquare, d ≤ |(gr p).det| := by
    intro p hp
    change d ≤ |(reflectedMetric g p).det|
    rw [reflectedMetric_det]
    exact hdet _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hcenterR : |hessianQuotient gr zr 0-(-q0)| ≤ 1/(100*boundedClassWidth kappa M) := by
    change |hessianQuotient (reflectedMetric g) (reflectedScalar z) 0-(-q0)| ≤ _
    rw [bounded_class_reflected_center hclass q0]
    exact hcenter
  have happR : ∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gr q i j-
        testMetric (reflectedMetric gStar) (-q0) (boundedClassWidth kappa M*r/16)
          N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau := by
    intro i j k hk p hp
    change ‖iteratedFDeriv ℝ k (fun q => reflectedMetric g q i j-
      testMetric (reflectedMetric gStar) (-q0) (boundedClassWidth kappa M*r/16)
        N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau
    rw [reflected_pulse_approximation_jet_norm]
    exact happ i j k hk _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hbound := hcauchyTau gr etaR UR WR zr YR
    (by simpa only [heR] using hgR) (reflectedDomain_isOpen hU)
    (by simpa only [heR] using hhR) (by simpa only [heR] using hfR)
    (by simpa only [heR] using hcR) (by simpa only [heR] using hg4R)
    (by simpa only [heR] using hdetR) (by simpa only [heR] using hcenterR)
    (by simpa only [heR] using happR) x hx n hn
  have he := sheared_reflected_Cauchy_jet_norms z q0 (-delta/(tau : ℝ)) x n
  change (‖iteratedFDeriv ℝ n (heightCauchyValue
      (heightInShearCoordinates (reflectedScalar z) (-q0)) (-delta/(tau : ℝ))) x‖ ≤ B ∧
    ‖iteratedFDeriv ℝ n (heightCauchyVelocity
      (heightInShearCoordinates (reflectedScalar z) (-q0)) (-delta/(tau : ℝ))) x‖ ≤ B) at hbound
  rw [he.1,he.2] at hbound
  simpa only [neg_div,neg_neg] using hbound

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_ActualClassTwoSidedCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Flow SmoothLocal.ODE
open SmoothLocal.HighEquation SmoothLocal.Weighted SmoothLocal.Taylor SmoothLocal.Model

theorem exists_actual_class_two_sided_cauchy_bounds_at_every_radius
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∃ G d : ℝ, 0 < G ∧ 0 < d ∧
      (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      (∀ a : ℝ, 0 < a → ∀ N : ℕ, 10 < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop,
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) ∧
            (∀ p ∈ modelSquare, d ≤ |(gTau p).det|)) ∧
      ∀ r : ℝ, 0 < r → r < 1/2 → boundedClassWidth kappa M*r ≤ 1/20 →
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) →
      ∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 10 < N → ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
              1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B) ∧
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B) := by
  obtain ⟨G,d,hG,hd,hGstar,hdstar,hlow⟩ :=
    exists_actual_low_metric_data_before_pulse_parameters hgStar hV hSV 8
  let L := boundedClassWidth kappa M
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hc : 0 < 1/(M : ℝ) := one_div_pos.mpr hMR
  refine ⟨G,d,hG,hd,hGstar,hdstar,?_,?_⟩
  · intro a ha N hN delta
    filter_upwards [hlow q0 a ha N (by omega) delta] with tau htau
    exact htau.2
  intro r hr hrhalf hLr hrsmall K
  obtain ⟨BL,hBL,hLbound⟩ := exists_actual_off_pulse_cauchy_bounds_at_radius
    hgStar hV hSV M hG.le hd hkappa hM hq0 hr hrhalf hLr hrsmall K
  obtain ⟨BU,hBU,hUbound⟩ := exists_actual_upper_off_pulse_cauchy_bounds_at_radius
    hgStar hV hSV M hG.le hd hkappa hM hq0 hr hrhalf hLr hrsmall K
  refine ⟨BL+BU,add_nonneg hBL hBU,?_⟩
  intro N hN delta hdelt
  have ha : 0 < L*r/16 := by positivity
  filter_upwards [hlow q0 (L*r/16) ha N (by omega) delta,
    hLbound N delta hdelt,hUbound N delta hdelt] with tau hlowTau hLTau hUTau
  intro eta z hclass hcenter happ x hx n hn
  obtain ⟨U,hU,hSU,hUV,hg0U,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
  have hlowActual := hlowTau.2 (perturbedMetric g0 eta.val) U hgU hU hSU happ
  have hg8 := hlowActual.1
  have hdet := hlowActual.2
  have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G :=
    fun i j k hk p hp => hg8 i j k (by omega) p hp
  have hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p :=
    fun p hp => hbackground p (hUV hp)
  obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
    hd hc hc hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
  have hleft := hLTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ x hx n hn
  have hright := hUTau g0 eta U z hg0U hgU hU hSU hmodel hh hclass hg8 hdet hcenter happ x hx n hn
  have hBLsum : BL ≤ BL+BU := by
    calc
      BL = BL+0 := by ring
      _ ≤ BL+BU := add_le_add le_rfl hBU
  have hBUsum : BU ≤ BL+BU := by
    calc
      BU = 0+BU := by ring
      _ ≤ BL+BU := add_le_add hBL le_rfl
  exact ⟨⟨hleft.1.trans hBLsum,hleft.2.trans hBLsum⟩,
    ⟨hright.1.trans hBUsum,hright.2.trans hBUsum⟩⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonSourceBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Taylor SmoothLocal.Hyperbolic

theorem exists_actual_comparison_source_pointwise_bound
    (B Bcompare BQ D A Cres : ℝ)
    {d dcompare c : ℝ} (hd : 0 < d) (hdcompare : 0 < dcompare) (hc : 0 < c)
    (hD : 0 ≤ D) (hA : 0 ≤ A) {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ H Cfirst Ctest Ccompare : ℝ,
      0 ≤ H ∧ 0 ≤ Cfirst ∧ 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U → SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ (z P : Coord → ℝ), ContDiffOn ℝ ∞ z U →
          ∀ epsilon epsilonQ : ℝ, epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
            epsilonQ ≤ 1 → (4*max BQ 0+2)*epsilonQ ≤ d/2 → H*epsilonQ ≤ c/2 →
            ∀ p : Coord,
              QPulsePointBounds gStar gTau z U q0 a delta tau N
                B Bcompare BQ D A d dcompare c epsilon epsilonQ p →
              |qResidual (metricInShearCoordinates gStar q0) P p| ≤ Cres/tau^N →
              |actualComparisonSource gStar gTau z q0 P p| ≤
                comparisonSourceBudget A Cfirst Ctest Ccompare Cres a ha N delta tau epsilon epsilonQ := by
  obtain ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,hglobal⟩ :=
    exists_actual_Q_pulse_forcing_bound_global B Bcompare BQ D A hd hdcompare hc hD hA ha N hN
  refine ⟨H,Cfirst,Ctest,Ccompare,hH,hCf,hCt,hCc,?_⟩
  intro delta hdelt
  obtain ⟨T,hT,hglobalT⟩ := hglobal delta hdelt
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU z P hz epsilon epsilonQ
    he1 hesmall heQ1 heQsmall hxxsmall p hpoint hres
  have htpos : 0 < tau := zero_lt_one.trans_le (hT.trans ht)
  have herr := hglobalT tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpoint.point_mem z hz
    epsilon epsilonQ hpoint.referenceFirst hpoint.referenceDet hpoint.testFirst hpoint.testDet
    hpoint.approximationFirst he1 hesmall hpoint.approximationSecond hpoint.referenceState
    hpoint.referenceXX hpoint.baseFirstDistance heQ1 heQsmall hxxsmall
    hpoint.actualDensity hpoint.referenceCoefficient
  have hlead : |actualShearedQLeading gStar z q0 a N delta tau p| ≤
      2*A*(pulseLeadingBound a ha*tau^2/tau^N) := by
    rw [actualShearedQLeading,abs_mul,abs_mul]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpoint.referenceCoefficient (by norm_num))
      (pulsePrincipalLeading_abs_bound ha htpos N delta p) (abs_nonneg _) (by positivity)
  have hforce : |actualShearedQForcing gStar gTau z q0 p| ≤
      2*A*(pulseLeadingBound a ha*tau^2/tau^N)+
        qForcingRemainderBudget A Cfirst Ctest Ccompare a ha N delta tau epsilon epsilonQ := by
    have htri : |actualShearedQForcing gStar gTau z q0 p| ≤
        |actualShearedQLeading gStar z q0 a N delta tau p|+
          |actualShearedQForcing gStar gTau z q0 p-actualShearedQLeading gStar z q0 a N delta tau p| := by
      have he : actualShearedQLeading gStar z q0 a N delta tau p+
          (actualShearedQForcing gStar gTau z q0 p-actualShearedQLeading gStar z q0 a N delta tau p) =
          actualShearedQForcing gStar gTau z q0 p := by ring
      simpa only [he] using abs_add_le (actualShearedQLeading gStar z q0 a N delta tau p)
        (actualShearedQForcing gStar gTau z q0 p-actualShearedQLeading gStar z q0 a N delta tau p)
    exact htri.trans (add_le_add hlead herr)
  exact (abs_sub _ _).trans (add_le_add hforce hres)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualClassComparisonGradient
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_comparison_gradient_from_source
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N : ℕ) (hN : 2 < N) :
    ∃ Cgradient : ℝ, 0 ≤ Cgradient ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
          (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          let zs := heightInShearCoordinates z q0
          let gs := metricInShearCoordinates gStar q0
          let P := taylorApproximation gs (-delta/(tau : ℝ))
            (heightCauchyValue zs (-delta/(tau : ℝ)))
            (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
          ∀ F : ℝ, 0 ≤ F →
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤ F) →
            ∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*F*delta/(tau : ℝ) := by
  let L := boundedClassWidth kappa M
  let Z := (2*(1+|q0|))^3*(M : ℝ)
  let nu := (boundedClassSpeed kappa M)^2/(2*(M : ℝ))
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hLrpos : 0 < L*r := mul_pos hL hr
  have hnu : 0 < nu := boundedClassShearHxxFloor_pos hkappa hM
  have hminv : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  obtain ⟨CP,A,_,hA,hsegment⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  let s0 := ((nu*(1/(M : ℝ)))/2)/A^2
  have hs0 : 0 < s0 := div_pos (half_pos (mul_pos hnu hminv))
    (sq_pos_of_pos (zero_lt_one.trans_le hA))
  have hgs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  obtain ⟨CE,hCE,hgradient⟩ := exists_actual_comparison_gradient hgs hVs
    (shearedModelSquare_isCompact q0) (shearedModelSquare_subset_domain hSV q0)
    1 CP Z (by norm_num) (half_pos hnu) hs0
  let speed := comparisonEnergySpeed CE
  let rate := comparisonEnergyRate CE CP Z s0
  let Cgradient := 2*Real.exp 1*Real.sqrt (2*(1+1/s0))*Real.sqrt (2*(L*r/4))
  have hs : 0 ≤ speed := add_nonneg (zero_le_one.trans hCE) (Real.sqrt_nonneg _)
  have hCg : 0 ≤ Cgradient := by dsimp [Cgradient] <;> positivity
  refine ⟨Cgradient,hCg,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  have hlarge : ∀ᶠ tau : ℕ in atTop, rate*(2*delta) ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  have hpulse : 0 < L*r/16 := div_pos hLrpos (by norm_num : (0 : ℝ) < 16)
  filter_upwards [hsegment delta hdelt hdhalf,hwidth,hlarge,
    comparison_pulse_geometry_eventually hpulse hs delta hdelt.le]
    with tau hsegTau hw hrateTau htravel
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gt := metricInShearCoordinates g q0
  let zs := heightInShearCoordinates z q0
  let a := -delta/(tau : ℝ)
  let b := delta/(tau : ℝ)
  let I := Ioo (-(L*r)) (L*r)
  let P := taylorApproximation gs a (heightCauchyValue zs a) (heightCauchyVelocity zs a) N
  let T := closedRectangle (-(L*r/2)) (L*r/2) a b
  have hTP : T = pulseStrip (L*r/2) delta (tau : ℝ) := by
    simp only [T,pulseStrip,a,b,neg_div]
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let D := (Us ∩ Vs) ∩ spatialStrip I
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hD : IsOpen D := (hUs.inter hVs).inter (spatialStrip_isOpen isOpen_Ioo)
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le hw.1
  have hbnonneg : 0 ≤ b := div_nonneg hdelt.le htpos.le
  have hab : a ≤ b := by dsimp only [a,b]; simp only [neg_div] <;> linarith
  have hbr : b ≤ r := by
    have he : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    dsimp only [b]
    rw [he]
    linarith [hw.2]
  have hcoordinates (p : Coord) (hp : p ∈ T) : |p 0| ≤ L*r ∧ |p 1| ≤ r := by
    have hx : |p 0| ≤ L*r/2 := abs_le.mpr hp.1
    have ht : |p 1| ≤ b := abs_le.mpr
      ⟨by simpa only [a,b,neg_div] using hp.2.1,hp.2.2⟩
    exact ⟨hx.trans (by linarith),ht.trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ T) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ T) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hbox : T ⊆ D := by
    intro p hp
    exact ⟨⟨hSU (hpS p hp),hSV (hpS p hp)⟩,
      ⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩⟩
  have hpoint (p : Coord) (hp : p ∈ T) : ‖p‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · change |p 0| ≤ 1
      exact (hcoordinates p hp).1.trans (hLr.trans (by norm_num))
    · change |p 1| ≤ 1
      exact (hcoordinates p hp).2.trans (by linarith)
  have hgt : SmoothPositiveOn gt D :=
    (metricInShearCoordinates_smoothPositive hg q0).mono (fun p hp => hp.1.1)
  have hzsUs : ContDiffOn ℝ ∞ zs Us := heightInShearCoordinates_contDiffOn hh.smooth q0
  have hzsD : ContDiffOn ℝ ∞ zs D := hzsUs.mono (fun p hp => hp.1.1)
  obtain ⟨hP,hPB,hsegActual⟩ := hsegTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hPD : ContDiffOn ℝ ∞ P D := hP.mono inter_subset_right
  have hzB : CoordinateBound zs T 3 Z := bounded_class_sheared_C3_on_actual_region hclass q0 hpS
  have hPB' : CoordinateBound P T 3 CP := by rw [hTP]; exact hPB
  have hCauchy := actual_taylor_Cauchy_of_smooth gs zs a N isOpen_Ioo hP
  have hpointEq (x t : ℝ) : boxPoint x t=(![x,t] : Coord) := by
    ext i
    fin_cases i
    · change x*1+t*0=x
      ring
    · change x*0+t*1=t
      ring
  have hvalue (x : ℝ) (hx : x ∈ Ioo (-(L*r/2)) (L*r/2)) :
      P (boxPoint x a)=zs (boxPoint x a) := by
    rw [hpointEq]
    exact (hCauchy x ⟨by linarith [hx.1],by linarith [hx.2]⟩).1
  have hvelocity (x : ℝ) (hx : x ∈ Ioo (-(L*r/2)) (L*r/2)) :
      coordPartial 1 P (boxPoint x a)=coordPartial 1 zs (boxPoint x a) := by
    rw [hpointEq]
    exact (hCauchy x ⟨by linarith [hx.1],by linarith [hx.2]⟩).2
  have hmargin (p : Coord) (hp : p ∈ T) (sigma : ℝ) (hsigma : sigma ∈ Icc (0 : ℝ) 1) :
      nu/2 ≤ |stateQDenominator gs (qHeightJetSegment P zs sigma p)| ∧
        s0 ≤ qFirstCoefficient gs 5 (qHeightJetSegment P zs sigma p) := by
    have hm := hsegActual p (by simpa only [hTP] using hp) sigma hsigma
    have he : nu/2=(boundedClassSpeed kappa M)^2/(4*(M : ℝ)) := by dsimp [nu] <;> ring
    exact ⟨by simpa only [he] using hm.1,hm.2.2.2.1⟩
  have htravel' : speed*(b-a) ≤ L*r/4-L*r/16 := by
    have he : b-a=2*delta/(tau : ℝ) := by dsimp [a,b] <;> ring
    rw [he]
    calc
      speed*(2*delta/(tau : ℝ)) ≤ 3*(L*r/16) := htravel.2.1
      _ = L*r/4-L*r/16 := by ring
  dsimp only
  intro F hF hsource theta htheta i
  have hsourceMetric (p : Coord) (hp : p ∈ T) :
      |metricComparisonSource gt gs P zs p| ≤ F := by
    change |actualComparisonSource gStar g z q0 P p| ≤ F
    exact hsource p (by simpa only [hTP] using hp)
  have hgrad := hgradient gt P zs D (L*r/2) (L*r/4) (L*r/16) a b F
    hD (fun p hp => hp.1.2) hgt hPD hzsD (by positivity) (by linarith) hab
    hbox (fun p hp => hpS p hp) hpoint hPB' hzB
    (fun p hp => (hgeom p hp).2.2.2.2.2.1)
    (fun p hp => abs_pos.mp (hnu.trans_le (hgeom p hp).2.1))
    hmargin hvalue hvelocity (by positivity) hF htravel'
    hsourceMetric theta
    (by simpa only [a,b,neg_div] using htheta) i
  have he : b-a=2*delta/(tau : ℝ) := by dsimp [a,b] <;> ring
  rw [he] at hgrad
  have hexp := comparison_exponential_le_fixed htpos hrateTau
  have hbound := mul_le_mul_of_nonneg_right hexp hF
  have hbound := mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg (2*(L*r/4)))
  have hduration : 0 ≤ 2*delta/(tau : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hdelt.le) htpos.le
  have hbound := mul_le_mul_of_nonneg_right hbound hduration
  have hbound := mul_le_mul_of_nonneg_left hbound (Real.sqrt_nonneg (2*(1+1/s0)))
  apply hgrad.trans
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [Cgradient]
  ring

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualQApplicability
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_Q_applicability_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N : ℕ) (hN : 2 < N) :
    ∃ Aref A D dcompare : ℝ, 1 ≤ Aref ∧ 0 ≤ A ∧ 0 ≤ D ∧ 0 < dcompare ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
        2 ≤ tau ∧ N ≤ tau ∧
        SmoothPositiveOn (testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ)) modelOpenSquare ∧
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
          (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            QPulsePointBounds gStar (perturbedMetric g0 eta.val) z modelOpenSquare q0
              (boundedClassWidth kappa M*r/16) delta (tau : ℝ) N
              (8*G) (G+1) (max (8*G) (boundedClassShearedStateBudget q0 M)) D A d dcompare
              ((boundedClassSpeed kappa M)^2/(4*(M : ℝ))) (metricApproximationAccuracy tau)
              (qPulseFirstJetBudget (boundedClassWidth kappa M*r/16)
                (div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)) N delta (tau : ℝ)) p ∧
            (1/(M : ℝ))/2 ≤ heightEnergy (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p ∧
            |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0| ≤ Aref ∧
            (metricInShearCoordinates gStar q0 p).det ≤ 2*G^2 ∧
            forcingFloor ((1/(M : ℝ))/2) (2*G^2) Aref ≤
              |forcingCoefficient (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p| ∧
            covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
              (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
  let L := boundedClassWidth kappa M
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hc : 0 < c := by
    have hh := boundedClassShearHxxFloor_pos hkappa hM
    have he : c=((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))/2 := by dsimp only [c] <;> ring
    rw [he]
    exact half_pos hh
  have he : 0 < (1/(M : ℝ))/2 := half_pos (one_div_pos.mpr (Nat.cast_pos.mpr hM))
  obtain ⟨_,Aref,_,hAref,hsegment⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨A,D,dcompare,hA,hD,hdcompare,hpoint⟩ := exists_actual_Q_point_bounds_from_reference_floor
    hgStar hV hSV M hG hd hc hgStarB hdStar hq0 hr hLr N (by omega)
  refine ⟨Aref,A,D,dcompare,hAref,hA,hD,hdcompare,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hsegment delta hdelt hdhalf,hpoint delta hdelt,hwidth] with tau hsTau hpTau hw
  refine ⟨hpTau.1,hpTau.2.1,hpTau.2.2.1,?_⟩
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates gStar q0
  let zs := heightInShearCoordinates z q0
  let S := pulseStrip (L*r/2) delta (tau : ℝ)
  have hs := (hsTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ).2.2
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have hcoordinates (p : Coord) (hp : p ∈ S) : |p 0| ≤ L*r ∧ |p 1| ≤ r :=
    ⟨(abs_le.mpr hp.1).trans (by linarith [mul_pos (boundedClassWidth_pos kappa M) hr]),
      (abs_le.mpr hp.2).trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ S) := actual_central_sheared_solution_margins
    eta hclass hG hd hkappa hr.le hLr hq0 hrsmall hgB hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hgs := metricInShearCoordinates_smoothPositive hgStar q0
  have hreference (p : Coord) (hp : p ∈ S) :
      c ≤ |covHessian gs zs p 0 0| ∧ |covHessian gs zs p 0 0| ≤ Aref ∧
        (1/(M : ℝ))/2 ≤ heightEnergy gs zs p := by
    have hm := hs p hp 1 (by norm_num)
    simp only [qHeightJetSegment,stateSegment_one,stateQDenominator_qSolutionJet] at hm
    have hE := hm.2.2.1
    unfold stateEnergy at hE
    rw [statePoint_qSolutionJet,stateGradient_qSolutionJet,
      jetEnergy_at_height hgs (hSV (hpS p hp)) zs] at hE
    exact ⟨hm.1,hm.2.1,hE⟩
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hQ := hpTau.2.2.2 g U z hg hU hSU hclass
    (fun i j k hk => hgB i j k (by omega)) hdet happ (fun p hp => (hreference p hp).1)
  intro p hp
  have href := hreference p hp
  have hdetup : (gs p).det ≤ 2*G^2 := by
    rw [metricDet_in_shear_coordinates]
    apply actual_det_upper_of_entry_bound gStar _ hG
    intro i j
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hgStarB i j 0 (by norm_num) _ (hpS p hp)
  have hforcing := forcingCoefficient_floor_of_reference_margins hgs (hSV (hpS p hp))
    he hc href.2.2 hdetup href.1 href.2.1
  have hactual : covHessian (metricInShearCoordinates g q0) zs p 0 0 ≠ 0 :=
    abs_pos.mp ((boundedClassShearHxxFloor_pos hkappa hM).trans_le (hgeom p hp).2.1)
  exact ⟨hQ p hp,href.2.2,href.2.1,hdetup,hforcing,hactual⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualClassComparisonSourceBound
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_comparison_source_bound_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N : ℕ) (hN : 2 < N) (Cres : ℝ) (hCres : 0 ≤ Cres) :
    ∃ Csource : ℝ, 0 < Csource ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
        1 ≤ tau ∧
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
          (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          ∀ P : Coord → ℝ,
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |qResidual (metricInShearCoordinates gStar q0) P p| ≤ Cres/(tau : ℝ)^N) →
            ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N := by
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  let BQ := max (8*G) (boundedClassShearedStateBudget q0 M)
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  have hc : 0 < c := by
    have hh := boundedClassShearHxxFloor_pos hkappa hM
    have he : c=((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))/2 := by dsimp only [c] <;> ring
    rw [he]
    exact half_pos hh
  obtain ⟨_,A,D,dcompare,_,hA,hD,hdcompare,happlicable⟩ :=
    exists_actual_Q_applicability_at_radius hgStar hV hSV M hG hd hgStarB hdStar
      hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨H,Cfirst,Ctest,Ccompare,_,hCf,_,hCc,hsource⟩ :=
    exists_actual_comparison_source_pointwise_bound (8*G) (G+1) BQ D A Cres
      hd hdcompare hc hD hA ha N (by omega)
  let Csource := 2*A*pulseLeadingBound a ha+1
  have hCs : 0 < Csource := by
    have hpulse := pulseLeadingBound_nonneg ha
    dsimp only [Csource]
    positivity
  refine ⟨Csource,hCs,?_⟩
  intro delta hdelt hdhalf
  obtain ⟨T,_,hsourceT⟩ := hsource delta hdelt
  let Q := 8+scalarPulseFirstJetBound a ha delta
  have hlarge : ∀ᶠ tau : ℕ in atTop,
      T ≤ (tau : ℝ) ∧
      comparisonLowerSourceCoefficient A Cfirst Ctest Ccompare Cres 1 Q a ha delta ≤ (tau : ℝ) := by
    apply (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (p := fun t : ℝ => T ≤ t ∧
        comparisonLowerSourceCoefficient A Cfirst Ctest Ccompare Cres 1 Q a ha delta ≤ t)
    filter_upwards [eventually_ge_atTop T,
      eventually_ge_atTop (comparisonLowerSourceCoefficient A Cfirst Ctest Ccompare Cres 1 Q a ha delta)]
      with t ht hscale
    exact ⟨ht,hscale⟩
  filter_upwards [happlicable delta hdelt hdhalf,
    actual_Q_approximation_eventual_margins (G+1) BQ H hd hdcompare hc ha N (by omega) delta,hlarge]
    with tau hactual hmarg hlargeTau
  rcases hmarg with ⟨ht2,_,_,heps1,hepsSmall,hepsScale,_,hepsQ1,hepsQSmall,hxxSmall⟩
  have ht1 : 1 ≤ tau := by omega
  have htR : (1 : ℝ) ≤ tau := by exact_mod_cast ht1
  refine ⟨ht1,?_⟩
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ P hres p hp
  let g := perturbedMetric g0 eta.val
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hOV : modelOpenSquare ⊆ V := modelOpenSquare_subset.trans hSV
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hgStarO : SmoothPositiveOn gStar modelOpenSquare :=
    ⟨fun i j => (hgStar.1 i j).mono hOV,fun p hp => hgStar.2 p (hOV hp)⟩
  have hzO := hh.smooth.mono hOU
  have hpoint := hactual.2.2.2 g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hb := hsourceT (tau : ℝ) hlargeTau.1 gStar g q0 modelOpenSquare hgStarO hactual.2.2.1 hgO
    modelOpenSquare_isOpen z P hzO (metricApproximationAccuracy tau)
    (qPulseFirstJetBudget a ha N delta (tau : ℝ))
    heps1 hepsSmall hepsQ1 hepsQSmall hxxSmall p (hpoint p hp).1 (hres p hp)
  apply hb.trans
  apply comparisonSourceBudget_le_leading (E := 1) (Q := Q) ha N hA hCf hCc hCres htR
  · simpa only [one_mul] using hepsScale
  · exact le_rfl
  · exact hlargeTau.2

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_ActualOffPulseCauchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix NNReal

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_off_pulse_cauchy_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
            (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
            CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
            CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
            (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
              ‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B := by
  let L := boundedClassWidth kappa M
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hMR : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hcut⟩ := exists_actual_finite_sheared_lower_cut_height_bounds
    (G := G) (Z := (M : ℝ)) (d := d) (c := 1/(M : ℝ)) (e0 := 1/(M : ℝ))
    (kappa := kappa) (q0 := q0) (L := L) hgStar hV hSV hG (Nat.cast_nonneg M) hd
      (one_div_pos.mpr hMR) hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro K
  obtain ⟨A0,hA0,hcutK⟩ := hcut (max 8 (K+2))
  let A : ℝ≥0 := ⟨A0,hA0⟩
  obtain ⟨Cmetric,hCmetric,hmetricK⟩ := exists_uniform_off_pulse_sheared_metric_bounds
    hgStar hV hSV hL hr hrhalf hLr hq0 (max 9 (K+3))
  obtain ⟨B,hB,hcauchy⟩ := exists_bounded_patch_cauchy_bound G d kappa q0 r Cmetric M A
    hG hd hkappa hM hr hrhalf hCmetric hq0 hLr hrsmall K
  refine ⟨B,hB,?_⟩
  intro N delta hdelt
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hcutK N delta hdelt,hwidth,
    eventually_ge_atTop (max 1 (max 9 (K+3)))] with tau hcutTau hwidthTau htau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ x hx n hn
  have htau1 : 1 ≤ tau := (le_max_left _ _).trans htau
  have htauk : max 9 (K+3) ≤ tau := (le_max_right _ _).trans htau
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau1)
  have hdw : delta/(tau : ℝ) ≤ r := by
    have he : delta/(tau : ℝ) = 2*(delta/(2*(tau : ℝ))) := by ring
    rw [he]
    linarith [hwidthTau.2]
  have hb0 : -delta/(tau : ℝ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hdelt.le) htr.le
  have hab : -r ≤ -delta/(tau : ℝ) := by simpa only [neg_div] using neg_le_neg hdw
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hfullMetric := hmetricK N delta hdelt tau htau1 htauk
    (perturbedMetric g0 eta.val) U hg hU hSU happ
  have hmetric : ∀ i j, CoordinateBound
      (fun p => metricInShearCoordinates (perturbedMetric g0 eta.val) q0 p i j)
      (shrinkingSlab (-(L*r)) (L*r) (-r) (-delta/(tau : ℝ)) (L/4)) (max 9 (K+3)) Cmetric := by
    intro i j ds hds p hp
    have haxes := shrinking_class_slab_axis_bounds hr.le hb0 hp
    exact hfullMetric i j ds hds p ⟨haxes.1,hp.1⟩
  have hactualCut : ∀ ds : List (Fin 2), ds.length ≤ max 8 (K+2) →
      ∀ x : ℝ, |x| ≤ L*r →
        |iteratedCoordPartial ds (heightInShearCoordinates z q0) (coordinatePoint x (-r))| ≤ (A : ℝ) :=
    hcutTau (perturbedMetric g0 eta.val) U W z Y hg hU hgB hdet hh hf hcenter happ
  exact hcauchy g0 eta z (-delta/(tau : ℝ)) hclass hab hb0 hgB hdet hcenter hmetric hactualCut x hx n hn

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_UniformTaylorStrip
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem uniform_taylor_strip
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (B : ℝ) (hB : 0 ≤ B) (N : ℕ) :
    ∃ epsilon R C : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 ≤ R ∧ 0 ≤ C ∧
      ∀ (u0 u1 : ℝ → ℝ) (I J : Set ℝ) (a : ℝ), IsOpen I → J ⊆ I →
      ContDiffOn ℝ ∞ u0 I → ContDiffOn ℝ ∞ u1 I →
      (∀ x ∈ I, (![x, a] : Coord) ∈ S) →
      (∀ x ∈ I, ‖qSolutionJet (linearCauchy a u0 u1) ![x, a]‖ ≤ M) →
      (∀ x ∈ I, c ≤ |covHessian g (linearCauchy a u0 u1) ![x, a] 0 0|) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u0 x‖ ≤ B) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u1 x‖ ≤ B) →
      ∀ b : ℝ, a ≤ b → b - a ≤ epsilon →
      (∀ x ∈ J, ∀ t ∈ Icc a b, (![x, t] : Coord) ∈ S) →
      let z0 := taylorApproximation g a u0 u1 N
      (∀ x ∈ J, ∀ t ∈ Icc a b, ∀ j ≤ taylorStripJetOrder N,
        ‖iteratedFDeriv ℝ j z0 ![x, t]‖ ≤ R) ∧
      (∀ x ∈ J, ∀ t ∈ Icc a b, c / 2 ≤ |covHessian g z0 ![x, t] 0 0|) ∧
      (∀ x ∈ J, ∀ t ∈ Icc a b,
        |iteratedDeriv N (fun s => qResidual g z0 ![x, s]) t| ≤ C) ∧
      (∀ x ∈ J, ∀ t ∈ Icc a b, |qResidual g z0 ![x, t]| ≤ C * (t - a)^N) := by
  obtain ⟨R, hR, hpoly⟩ := uniform_taylorApproximation_jets hg hU hS hSU M hM hc B hB
    N (taylorStripJetOrder N)
  obtain ⟨epsilon, he, he1, hwidth⟩ := exists_uniform_Hxx_strip_width hg hU hS hSU R hR hc
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (fun p : Coord => p) S)
  let A0 := max A 0
  have hA0 : 0 ≤ A0 := le_max_right _ _
  have hpoint : ∀ p ∈ S, ‖p‖ ≤ A0 := fun p hp => (hA p hp).trans (le_max_left _ _)
  obtain ⟨C0, hC0, hresidual⟩ := exists_uniform_qResidual_fullJet_bound hg hU hS hSU
    (max A0 R) (hA0.trans (le_max_left _ _)) (half_pos hc) N
  let C := R + (N.factorial : ℝ) * C0 * (max 1 R)^N
  have hC : 0 ≤ C := by dsimp [C] <;> positivity
  refine ⟨epsilon, R, C, he, he1, hR, hC, ?_⟩
  intro u0 u1 I J a hI hJI h0 h1 hcut hstate hden h0B h1B b hab hba hstrip
  dsimp only
  have hxx0 : ∀ x ∈ I, covHessian g (linearCauchy a u0 u1) ![x, a] 0 0 ≠ 0 := by
    intro x hx hh
    have hd := hden x hx
    rw [hh, abs_zero] at hd
    linarith
  obtain ⟨hP, hjet, hzero⟩ := taylorApproximation_properties hg hU hI h0 h1 a
    (fun x hx => hSU (hcut x hx)) hxx0 N
  have hfull := hpoly u0 u1 I J a hI hJI h0 h1 hcut hstate hden h0B h1B
  have htime (t : ℝ) (ht : t ∈ Icc a b) : |t - a| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    exact (sub_le_sub_right ht.2 a).trans (hba.trans he1)
  have hfull' : ∀ x ∈ J, ∀ t ∈ Icc a b, ∀ j ≤ taylorStripJetOrder N,
      ‖iteratedFDeriv ℝ j (taylorApproximation g a u0 u1 N) ![x, t]‖ ≤ R := by
    intro x hx t ht j hj
    exact hfull j hj ![x, t] hx (htime t ht)
  have hden0 : ∀ x ∈ I,
      c ≤ |covHessian g (taylorApproximation g a u0 u1 N) ![x, a] 0 0| := by
    intro x hx
    rw [← stateQDenominator_qSolutionJet, hjet x hx, stateQDenominator_qSolutionJet]
    exact hden x hx
  have hdenAll : ∀ x ∈ J, ∀ t ∈ Icc a b,
      c / 2 ≤ |covHessian g (taylorApproximation g a u0 u1 N) ![x, t] 0 0| := by
    intro x hx t ht
    apply hwidth (taylorApproximation g a u0 u1 N) I hI hP a t x ht.1
      ((sub_le_sub_right ht.2 a).trans hba) (hJI hx)
    · intro s hs
      exact hstrip x hx s ⟨hs.1, hs.2.trans ht.2⟩
    · intro s hs j hj
      exact hfull' x hx s ⟨hs.1, hs.2.trans ht.2⟩ j
        (hj.trans (le_max_left _ _))
    · exact hden0 x (hJI hx)
  have hne : ∀ x ∈ J, ∀ t ∈ Icc a b,
      covHessian g (taylorApproximation g a u0 u1 N) ![x, t] 0 0 ≠ 0 := by
    intro x hx t ht hh
    have hd := hdenAll x hx t ht
    rw [hh, abs_zero] at hd
    linarith
  have hstateAll : ∀ x ∈ J, ∀ t ∈ Icc a b,
      ‖qSolutionJet (taylorApproximation g a u0 u1 N) ![x, t]‖ ≤ max A0 R := by
    intro x hx t ht
    apply qSolutionJet_norm_bound hP (spatialStrip_isOpen hI) (hJI hx) hA0 hR
      (hpoint _ (hstrip x hx t ht))
    intro j hj
    exact hfull' x hx t ht j (hj.trans (by unfold taylorStripJetOrder; omega))
  have hresBound : ∀ x ∈ J, ∀ t ∈ Icc a b,
      ‖iteratedFDeriv ℝ N (qResidual g (taylorApproximation g a u0 u1 N)) ![x, t]‖ ≤ C := by
    intro x hx t ht
    exact hresidual (taylorApproximation g a u0 u1 N) I hI hP ![x, t] (hJI hx)
      (hstrip x hx t ht) (hstateAll x hx t ht) (hdenAll x hx t ht) N le_rfl R
      (fun j hj => hfull' x hx t ht j (hj.trans (le_max_right _ _)))
  have htimeBound : ∀ x ∈ J, ∀ t ∈ Icc a b,
      |iteratedDeriv N (fun s => qResidual g (taylorApproximation g a u0 u1 N) ![x, s]) t| ≤ C := by
    intro x hx t ht
    exact (qResidual_time_jet_le_fullJet hg hU hI hP x t (hJI hx)
      (hSU (hstrip x hx t ht)) (hne x hx t ht) N).trans (hresBound x hx t ht)
  refine ⟨hfull', hdenAll, htimeBound, ?_⟩
  intro x hx t ht
  apply zero_jets_remainder_bound hab ?_ N (hzero x (hJI hx)) hC
    (htimeBound x hx) ht
  intro s hs
  exact ((qResidual_contDiffOn hg hU hI hP).contDiffAt
    ((comparisonDomain_isOpen hg hU hI hP).mem_nhds
      (mem_comparisonDomain (hJI hx) (hSU (hstrip x hx s hs)) (hne x hx s hs)))).comp s
        (verticalPoint_contDiff x).contDiffAt

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_UniformTaylorPulse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem uniform_taylor_pulse
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) (hM : 0 ≤ M) {c : ℝ} (hc : 0 < c) (B : ℝ) (hB : 0 ≤ B) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1 / 2 →
      ∃ tau0 : ℕ, 0 < tau0 ∧ ∀ tau : ℕ, tau0 ≤ tau →
      ∀ (u0 u1 : ℝ → ℝ) (I J : Set ℝ), IsOpen I → J ⊆ I →
      ContDiffOn ℝ ∞ u0 I → ContDiffOn ℝ ∞ u1 I →
      (∀ x ∈ I, (![x, -delta / (tau : ℝ)] : Coord) ∈ S) →
      (∀ x ∈ I, ‖qSolutionJet (linearCauchy (-delta / (tau : ℝ)) u0 u1)
        ![x, -delta / (tau : ℝ)]‖ ≤ M) →
      (∀ x ∈ I, c ≤ |covHessian g (linearCauchy (-delta / (tau : ℝ)) u0 u1)
        ![x, -delta / (tau : ℝ)] 0 0|) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u0 x‖ ≤ B) →
      (∀ x ∈ J, ∀ j ≤ taylorInitialRequest N (taylorStripJetOrder N),
        ‖iteratedFDeriv ℝ j u1 x‖ ≤ B) →
      (∀ x ∈ J, ∀ t ∈ Icc (-delta / (tau : ℝ)) (delta / (tau : ℝ)),
        (![x, t] : Coord) ∈ S) →
      let z0 := taylorApproximation g (-delta / (tau : ℝ)) u0 u1 N
      ContDiffOn ℝ ∞ z0 (spatialStrip I) ∧
      (∀ x ∈ I, z0 ![x, -delta / (tau : ℝ)] = u0 x ∧
        coordPartial 1 z0 ![x, -delta / (tau : ℝ)] = u1 x) ∧
      (∀ x, ∃ p : Polynomial ℝ, p.natDegree ≤ N + 1 ∧ ∀ t, p.eval t = z0 ![x, t]) ∧
      (∀ x ∈ J, ∀ t ∈ Icc (-delta / (tau : ℝ)) (delta / (tau : ℝ)),
        c / 2 ≤ |covHessian g z0 ![x, t] 0 0| ∧
        |qResidual g z0 ![x, t]| ≤ C / (tau : ℝ)^N) := by
  obtain ⟨epsilon, _, C, he, _, _, hC, hstrip⟩ := uniform_taylor_strip
    hg hU hS hSU M hM hc B hB N
  refine ⟨C, hC, ?_⟩
  intro delta hd hdhalf
  obtain ⟨tau0, htau0, hwidth⟩ := exists_pulse_width_threshold he hd
  refine ⟨tau0, htau0, ?_⟩
  intro tau htau u0 u1 I J hI hJI h0 h1 hcut hstate hden h0B h1B hregion
  obtain ⟨htaupos, hthin⟩ := hwidth tau htau
  have htr : (0 : ℝ) < tau := Nat.cast_pos.mpr htaupos
  have hab : -delta / (tau : ℝ) ≤ delta / (tau : ℝ) := by
    exact div_le_div_of_nonneg_right (by linarith) htr.le
  have hwidth' : delta / (tau : ℝ) - (-delta / (tau : ℝ)) ≤ epsilon := by
    convert hthin using 1 <;> first | rfl | ring
  have hdata := hstrip u0 u1 I J (-delta / (tau : ℝ)) hI hJI h0 h1 hcut hstate hden
    h0B h1B (delta / (tau : ℝ)) hab hwidth' hregion
  have hxx : ∀ x ∈ I,
      covHessian g (linearCauchy (-delta / (tau : ℝ)) u0 u1)
        ![x, -delta / (tau : ℝ)] 0 0 ≠ 0 := by
    intro x hx hh
    have hd' := hden x hx
    rw [hh, abs_zero] at hd'
    linarith
  obtain ⟨hP, hinitial, hdegree, _, _⟩ := finiteTaylorComparison hg hU hI h0 h1
    (-delta / (tau : ℝ)) (fun x hx => hSU (hcut x hx)) hxx N
  refine ⟨hP, hinitial, hdegree, ?_⟩
  intro x hx t ht
  exact ⟨hdata.2.1 x hx t ht, (hdata.2.2.2 x hx t ht).trans
    (pulse_time_power_bound hd hdhalf htaupos hC ht)⟩

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ActualUniformTaylorPulse
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_uniform_taylor_pulse
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
            (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
            CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
            CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
            (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            let zs := heightInShearCoordinates z q0
            let gs := metricInShearCoordinates gStar q0
            let z0 := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ z0 (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              z0 ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 z0 ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ P : Polynomial ℝ, P.natDegree ≤ N+1 ∧ ∀ t, P.eval t = z0 ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs z0 ![x,t] 0 0| ∧
                |qResidual gs z0 ![x,t]| ≤ C/(tau : ℝ)^N) := by
  let L := boundedClassWidth kappa M
  let gs := metricInShearCoordinates gStar q0
  let Vs := inverseShearCoordinates q0 ⁻¹' V
  let S := shearedModelSquare q0
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hgs : SmoothPositiveOn gs Vs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs : IsOpen Vs := shearedModelDomain_isOpen hV q0
  have hS : IsCompact S := shearedModelSquare_isCompact q0
  have hSVs : S ⊆ Vs := shearedModelSquare_subset_domain hSV q0
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hCauchy⟩ :=
    exists_actual_off_pulse_cauchy_bounds hgStar hV hSV M hG hd hkappa hM hq0
  obtain ⟨tauRef,htauRef,hfloor⟩ := exists_bounded_patch_reference_initial_floor
    G kappa d q0 M hG hkappa hd hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N
  let K := taylorInitialRequest N (taylorStripJetOrder N)
  obtain ⟨B,hB,hCauchyK⟩ := hCauchy K
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  have hc : 0 < c := div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  obtain ⟨C,hC,hTaylor⟩ := uniform_taylor_pulse hgs hVs hS hSVs
    (initialShearedStateBudget (M : ℝ) q0) (initialShearedStateBudget_nonneg _ _) hc B hB N
  refine ⟨C,hC,?_⟩
  intro delta hdelt hdhalf
  obtain ⟨tauTaylor,_,hpoly⟩ := hTaylor delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hCauchyK N delta hdelt,hwidth,
    eventually_ge_atTop (max tauTaylor tauRef)] with tau hCauchyTau hwidthTau htau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let a := -delta/(tau : ℝ)
  let zs := heightInShearCoordinates z q0
  let I := Ioo (-(L*r)) (L*r)
  let J := Icc (-(L*r/2)) (L*r/2)
  have htauT : tauTaylor ≤ tau := (le_max_left _ _).trans htau
  have htauR : tauRef ≤ tau := (le_max_right _ _).trans htau
  have htau1 : 1 ≤ tau := htauRef.trans htauR
  have htauPos : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast htau1)
  have hdw : delta/(tau : ℝ) ≤ r := by
    have he : delta/(tau : ℝ) = 2*(delta/(2*(tau : ℝ))) := by ring
    rw [he]
    linarith [hwidthTau.2]
  have habs : |a| ≤ r := by
    dsimp only [a]
    rw [abs_div,abs_neg,abs_of_pos hdelt,abs_of_pos htauPos]
    exact hdw
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hcutS (x : ℝ) (hx : x ∈ I) : inverseShearCoordinates q0 ![x,a] ∈ modelSquare := by
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨abs_le.mpr ⟨hx.1.le,hx.2.le⟩,habs⟩
  have hcutU (x : ℝ) (hx : x ∈ I) : (![x,a] : Coord) ∈ inverseShearCoordinates q0 ⁻¹' U :=
    hSU (hcutS x hx)
  have hzs : ContDiffOn ℝ ∞ zs (inverseShearCoordinates q0 ⁻¹' U) :=
    heightInShearCoordinates_contDiffOn hh.smooth q0
  have hUs := shearedModelDomain_isOpen hU q0
  have hI : IsOpen I := isOpen_Ioo
  have hJI : J ⊆ I := by
    intro x hx
    exact ⟨by linarith [hx.1,mul_pos hL hr],by linarith [hx.2,mul_pos hL hr]⟩
  have hstate (x : ℝ) (hx : x ∈ I) :
      ‖qSolutionJet (linearCauchy a (heightCauchyValue zs a) (heightCauchyVelocity zs a)) ![x,a]‖ ≤
        initialShearedStateBudget (M : ℝ) q0 := by
    apply actual_initial_sheared_state_bound hh.smooth hU hSU (Nat.cast_nonneg M) hh.lowJet
      q0 (-(L*r)) (L*r) a hcutS hx
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · change ‖x‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact (abs_le.mpr ⟨hx.1.le,hx.2.le⟩).trans (hLr.trans (by norm_num))
    · change ‖a‖ ≤ 1
      rw [Real.norm_eq_abs]
      exact habs.trans (by linarith)
  have hden := hfloor g0 gStar V eta z r N delta tau hgStar hV hSV hclass hr hLr hrsmall
    hgB hdet hcenter hdelt htauR hdw happ
  have hBactual := hCauchyTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have h0 := heightCauchyValue_contDiffOn hzs a hcutU
  have h1 := heightCauchyVelocity_contDiffOn hzs hUs a hcutU
  have hregion (x : ℝ) (hx : x ∈ J) (t : ℝ)
      (ht : t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ))) : (![x,t] : Coord) ∈ S :=
    pulseRectangle_mem_shearedModelSquare hL hr hrhalf hLr hq0 hdw (abs_le.mpr hx) ht
  have hresult := hpoly tau htauT (heightCauchyValue zs a) (heightCauchyVelocity zs a) I J hI hJI h0 h1
    (fun x hx => hcutS x hx) hstate hden
    (fun x hx k hk => (hBactual x (abs_le.mpr hx) k hk).1)
    (fun x hx k hk => (hBactual x (abs_le.mpr hx) k hk).2) hregion
  refine ⟨hresult.1,hresult.2.1,hresult.2.2.1,?_⟩
  intro x hx t ht
  have hh := hresult.2.2.2 x (abs_le.mp hx) t ht
  have he : c/2 = (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) := by dsimp [c] <;> ring
  exact ⟨he ▸ hh.1,hh.2⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ActualUniformTaylorRich
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_uniform_taylor_comparison_and_moment
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
            (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
            CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
            CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G) →
            (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            let zs := heightInShearCoordinates z q0
            let gs := metricInShearCoordinates gStar q0
            let z0 := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ z0 (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              z0 ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 z0 ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ P : Polynomial ℝ, P.natDegree ≤ N+1 ∧ ∀ t, P.eval t = z0 ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs z0 ![x,t] 0 0| ∧
                |qResidual gs z0 ![x,t]| ≤ C/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs z0)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs z0)| ≤
              (2*C*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hTaylor⟩ :=
    exists_actual_uniform_taylor_pulse hgStar hV hSV M hG hd hkappa hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N
  obtain ⟨C,hC,hN⟩ := hTaylor N
  refine ⟨C,hC,?_⟩
  intro delta hdelt hdhalf
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hN delta hdelt hdhalf,hwidth] with tau htaylor hwidthTau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have ht := htaylor g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let gs := metricInShearCoordinates gStar q0
  let zs := heightInShearCoordinates z q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ)))
    (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  let I := Ioo (-(L*r)) (L*r)
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have ha : 0 < a := div_pos (mul_pos hL hr) (by norm_num)
  have htr : (0 : ℝ) < tau := zero_lt_one.trans_le hwidthTau.1
  have hdw : delta/(tau : ℝ) ≤ r := by
    have he : delta/(tau : ℝ) = 2*(delta/(2*(tau : ℝ))) := by ring
    rw [he]
    linarith [hwidthTau.2]
  have hP : ContDiffOn ℝ ∞ P (spatialStrip I) := ht.1
  have hpoint (p : Coord) (hp : p ∈ pulseStrip a delta (tau : ℝ)) :
      (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P p 0 0| ∧
      |qResidual gs P p| ≤ C/(tau : ℝ)^N := by
    have hx : |p 0| ≤ L*r/2 := (abs_le.mpr hp.1).trans (by dsimp [a] <;> nlinarith [mul_pos hL hr])
    have htime : p 1 ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)) := by
      simpa only [neg_div] using hp.2
    have he : ![p 0,p 1] = p := by ext i; fin_cases i <;> rfl
    simpa only [he] using ht.2.2.2 (p 0) hx (p 1) htime
  have hgs := metricInShearCoordinates_smoothPositive hgStar q0
  have hVs := shearedModelDomain_isOpen hV q0
  have hc : 0 < (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) :=
    div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
      (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  have hsub : pulseStrip a delta (tau : ℝ) ⊆
      comparisonDomain gs (inverseShearCoordinates q0 ⁻¹' V) P I := by
    intro p hp
    have hx : |p 0| ≤ L*r/2 := (abs_le.mpr hp.1).trans (by dsimp [a] <;> nlinarith [mul_pos hL hr])
    have hpI : p ∈ spatialStrip I := by
      exact ⟨by linarith [(abs_le.mp hx).1,mul_pos hL hr],
        by linarith [(abs_le.mp hx).2,mul_pos hL hr]⟩
    have htime : p 1 ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)) := by
      simpa only [neg_div] using hp.2
    have he : ![p 0,p 1] = p := by ext i; fin_cases i <;> rfl
    have hpS : p ∈ shearedModelSquare q0 := by
      simpa only [he] using pulseRectangle_mem_shearedModelSquare hL hr hrhalf hLr hq0 hdw hx htime
    exact mem_comparisonDomain hpI (shearedModelSquare_subset_domain hSV q0 hpS)
      (abs_pos.mp (hc.trans_le (hpoint p hp).1))
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,
    (qResidual_contDiffOn hgs hVs isOpen_Ioo hP).continuousOn.mono hsub,?_⟩
  apply (pulseWeightedMoment_bound ha hdelt.le htr (div_nonneg hC (pow_nonneg htr.le N))
    (fun p hp => (hpoint p hp).2)).trans_eq
  rw [pow_succ]
  field_simp [htr.ne']
  ring

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualUniformComparisonGradient
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_uniform_comparison_gradient
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ N : ℕ, 2 < N → ∃ Cres Csource Cgradient : ℝ,
        0 ≤ Cres ∧ 0 < Csource ∧ 0 ≤ Cgradient ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
            (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
            CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
            CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
            (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            let zs := heightInShearCoordinates z q0
            let gs := metricInShearCoordinates gStar q0
            let P := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              P ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 P ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ Q : Polynomial ℝ, Q.natDegree ≤ N+1 ∧ ∀ t, Q.eval t = P ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P ![x,t] 0 0| ∧
                |qResidual gs P ![x,t]| ≤ Cres/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs P)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs P)| ≤
              (2*Cres*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) ∧
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N) ∧
            (∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*delta*(tau : ℝ)/(tau : ℝ)^N) := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hTaylor⟩ :=
    exists_actual_uniform_taylor_comparison_and_moment hgStar hV hSV M hG hd hkappa hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N hN
  obtain ⟨Cres,hCres,hTaylorN⟩ := hTaylor N
  obtain ⟨Csource,hCsource,hsource⟩ := exists_actual_class_comparison_source_bound_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN Cres hCres
  obtain ⟨CE,hCE,hgradient⟩ := exists_actual_class_comparison_gradient_from_source
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  refine ⟨Cres,Csource,CE*Csource,hCres,hCsource,mul_nonneg hCE hCsource.le,?_⟩
  intro delta hdelt hdhalf
  filter_upwards [hTaylorN delta hdelt hdhalf,hsource delta hdelt hdhalf,hgradient delta hdelt hdhalf]
    with tau htaylor hsourceTau hgradientTau
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let L := boundedClassWidth kappa M
  let zs := heightInShearCoordinates z q0
  let gs := metricInShearCoordinates gStar q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ)))
    (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  have ht := htaylor g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hres (p : Coord) (hp : p ∈ pulseStrip (L*r/2) delta (tau : ℝ)) :
      |qResidual gs P p| ≤ Cres/(tau : ℝ)^N := by
    have he : ![p 0,p 1] = p := by ext i; fin_cases i <;> rfl
    have htime : p 1 ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)) := by
      simpa only [neg_div] using hp.2
    simpa only [he] using (ht.2.2.2.1 (p 0) (abs_le.mpr hp.1) (p 1) htime).2
  have hs := hsourceTau.2 g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ P hres
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2.1,ht.2.2.2.2.1,ht.2.2.2.2.2,hs,?_⟩
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le (by exact_mod_cast hsourceTau.1)
  have hF : 0 ≤ Csource*(tau : ℝ)^2/(tau : ℝ)^N := by positivity
  intro theta htheta i
  have hgrad := hgradientTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
    (Csource*(tau : ℝ)^2/(tau : ℝ)^N) hF hs theta htheta i
  apply hgrad.trans_eq
  field_simp [htpos.ne']

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ActualClassQForcingMoment
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_Q_forcing_moment_at_radius
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20)
    (hr : 0 < r) (hrhalf : r < 1/2) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (N : ℕ) (hN : 2 < N) :
    ∃ c3 : ℝ, 0 < c3 ∧ ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 →
      ∀ᶠ tau : ℕ in atTop,
        ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
          (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
          SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
          CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
          CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
          BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
          (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
          |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          c3*delta*(tau : ℝ)/(tau : ℝ)^N ≤
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ)
              (actualShearedQForcing gStar (perturbedMetric g0 eta.val) z q0)| := by
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let c := (boundedClassSpeed kappa M)^2/(4*(M : ℝ))
  let e := (1/(M : ℝ))/2
  let BQ := max (8*G) (boundedClassShearedStateBudget q0 M)
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  have hc : 0 < c := by
    have hh := boundedClassShearHxxFloor_pos hkappa hM
    have heq : c=((boundedClassSpeed kappa M)^2/(2*(M : ℝ)))/2 := by dsimp only [c] <;> ring
    rw [heq]
    exact half_pos hh
  have he : 0 < e := half_pos (one_div_pos.mpr (Nat.cast_pos.mpr hM))
  obtain ⟨Aref,A,D,dcompare,_,hA,hD,hdcompare,happlicable⟩ :=
    exists_actual_Q_applicability_at_radius hgStar hV hSV M hG hd hgStarB hdStar
      hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨c3,H,_,_,_,hc3,_,_,_,_,hforcing⟩ :=
    exists_actual_Q_moment_positive_lower (8*G) (G+1) BQ D A (2*G^2) Aref
      hd hdcompare hc he hD hA ha N (by omega)
  refine ⟨c3,hc3,?_⟩
  intro delta hdelt hdhalf
  obtain ⟨T,_,hforcingT⟩ := hforcing delta hdelt
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  filter_upwards [happlicable delta hdelt hdhalf,
    actual_Q_approximation_eventual_margins (G+1) BQ H hd hdcompare hc ha N (by omega) delta,hlarge]
    with tau hactual hmarg ht
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  have hSU : modelSquare ⊆ U := hf.squareSubset.trans hf.domainSubset
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hOV : modelOpenSquare ⊆ V := modelOpenSquare_subset.trans hSV
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hgStarO : SmoothPositiveOn gStar modelOpenSquare :=
    ⟨fun i j => (hgStar.1 i j).mono hOV,fun p hp => hgStar.2 p (hOV hp)⟩
  have hzO := hh.smooth.mono hOU
  have hpoint := hactual.2.2.2 g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hsubset : pulseStrip a delta (tau : ℝ) ⊆ pulseStrip (L*r/2) delta (tau : ℝ) := by
    intro p hp
    refine ⟨⟨?_,?_⟩,hp.2⟩ <;> dsimp only [a] at hp <;>
      linarith [hp.1.1,hp.1.2,mul_pos (boundedClassWidth_pos kappa M) hr]
  rcases hmarg with ⟨_,_,heps,heps1,hepsSmall,hepsScale,hepsQ,hepsQ1,hepsQSmall,hxxSmall⟩
  exact hforcingT (tau : ℝ) ht gStar g q0 modelOpenSquare hgStarO hactual.2.2.1 hgO
    modelOpenSquare_isOpen z hzO (metricApproximationAccuracy tau) (qPulseFirstJetBudget a ha N delta (tau : ℝ))
      heps hepsQ heps1 hepsSmall hepsQ1 hepsQSmall hxxSmall hepsScale le_rfl
      (fun p hp => (hpoint p (hsubset hp)).1)
      (fun p hp => (hpoint p (hsubset hp)).2.2.2.2.2)
      (fun p hp => (hpoint p (hsubset hp)).2.1)
      (fun p hp => (hpoint p (hsubset hp)).2.2.2.1)
      (fun p hp => (hpoint p (hsubset hp)).2.2.1)

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualClassComparisonMoment
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_class_comparison_moment
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d kappa q0 : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hkappa : 0 < kappa) (hM : 0 < M) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      ∀ N : ℕ, 2 < N → ∃ C Csource Cgradient c3 : ℝ,
        0 ≤ C ∧ 0 < Csource ∧ 0 ≤ Cgradient ∧ 0 < c3 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
          ∀ (g0 : MetricField) (eta : metricPatchSet g0 kappa) (U W : Set Coord)
            (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
            SmoothPositiveOn (perturbedMetric g0 eta.val) U → IsOpen U →
            CapInductionHeight (perturbedMetric g0 eta.val) U (M : ℝ) (1/(M : ℝ)) (1/(M : ℝ)) z →
            CapInductionFlow (perturbedMetric g0 eta.val) U G (M : ℝ) d (1/(M : ℝ)) (1/(M : ℝ)) kappa z Y W →
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            (∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G) →
            (∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|) →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            let zs := heightInShearCoordinates z q0
            let gs := metricInShearCoordinates gStar q0
            let P := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              P ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 P ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ poly : Polynomial ℝ, poly.natDegree ≤ N+1 ∧ ∀ t, poly.eval t = P ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P ![x,t] 0 0| ∧
                |qResidual gs P ![x,t]| ≤ C/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs P) (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs P)| ≤
              (2*C*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) ∧
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N) ∧
            (∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*delta*(tau : ℝ)/(tau : ℝ)^N) ∧
            ContinuousOn (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            c3*delta*(tau : ℝ)/(tau : ℝ)^N ≤
              |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ)
                (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)| := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hTaylor⟩ :=
    exists_actual_uniform_comparison_gradient hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro N hN
  let L := boundedClassWidth kappa M
  let a := L*r/16
  have ha : 0 < a := div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  obtain ⟨C,Csource,Cgradient,hC,hCsource,hCgradient,hTaylorN⟩ := hTaylor N hN
  obtain ⟨cQ,hcQ,hQmoment⟩ := exists_actual_class_Q_forcing_moment_at_radius
    hgStar hV hSV M hG hd hgStarB hdStar hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  obtain ⟨Aref,A,D,dcompare,_,_,_,_,happlicable⟩ :=
    exists_actual_Q_applicability_at_radius hgStar hV hSV M hG hd hgStarB hdStar
      hkappa hM hq0 hr hrhalf hLr hrsmall N hN
  let R := 2*C*(∫ x : ℝ, axisBump a x)
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (by norm_num) hC) (axisBump_integral_pos ha).le
  obtain ⟨T,_,habsorb⟩ := taylor_moment_absorption_threshold hR hcQ N
  refine ⟨C,Csource,Cgradient,cQ/2,hC,hCsource,hCgradient,half_pos hcQ,?_⟩
  intro delta hdelt hdhalf
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  filter_upwards [hTaylorN delta hdelt hdhalf,hQmoment delta hdelt hdhalf,
    happlicable delta hdelt hdhalf,hlarge] with tau hTaylorTau hQTau hATau ht
  intro g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  let g := perturbedMetric g0 eta.val
  let gs := metricInShearCoordinates gStar q0
  let zs := heightInShearCoordinates z q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  have hTaylorActual := hTaylorTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hQlower := hQTau g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hpoint := hATau.2.2.2 g0 eta U W z Y hg hU hh hf hclass hgB hdet hcenter happ
  have hsub : pulseStrip a delta (tau : ℝ) ⊆ pulseStrip (L*r/2) delta (tau : ℝ) := by
    intro p hp
    refine ⟨⟨?_,?_⟩,hp.2⟩ <;> dsimp only [a] at hp <;>
      linarith [hp.1.1,hp.1.2,mul_pos (boundedClassWidth_pos kappa M) hr]
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans (hf.squareSubset.trans hf.domainSubset)
  have hOV : modelOpenSquare ⊆ V := modelOpenSquare_subset.trans hSV
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hgStarO : SmoothPositiveOn gStar modelOpenSquare :=
    ⟨fun i j => (hgStar.1 i j).mono hOV,fun p hp => hgStar.2 p (hOV hp)⟩
  have hzO := hh.smooth.mono hOU
  have hSU : ∀ p ∈ pulseStrip a delta (tau : ℝ), inverseShearCoordinates q0 p ∈ modelOpenSquare :=
    fun p hp => (hpoint p (hsub hp)).1.point_mem
  have hc : 0 < (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) :=
    div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM)) (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  have hxxRef : ∀ p ∈ pulseStrip a delta (tau : ℝ), covHessian gs zs p 0 0 ≠ 0 :=
    fun p hp => abs_pos.mp (hc.trans_le (hpoint p (hsub hp)).1.referenceXX)
  have hxxActual : ∀ p ∈ pulseStrip a delta (tau : ℝ),
      covHessian (metricInShearCoordinates g q0) zs p 0 0 ≠ 0 :=
    fun p hp => (hpoint p (hsub hp)).2.2.2.2.2
  have hQc : ContinuousOn (actualShearedQForcing gStar g z q0) (pulseStrip a delta (tau : ℝ)) :=
    ((sheared_Q_on_height_contDiffOn hgO hzO modelOpenSquare_isOpen q0 hSU hxxActual).sub
      (sheared_Q_on_height_contDiffOn hgStarO hzO modelOpenSquare_isOpen q0 hSU hxxRef)).continuousOn
  have hPc : ContinuousOn (qResidual gs P) (pulseStrip a delta (tau : ℝ)) := hTaylorActual.2.2.2.2.1
  have hPres := hTaylorActual.2.2.2.2.2.1
  have htriangle := actualComparisonSource_moment_triangle hQc hPc
  have habs := habsorb (tau : ℝ) ht delta hdelt.le
  change |pulseWeightedMoment a delta (tau : ℝ) (qResidual gs P)| ≤ R*delta/(tau : ℝ)^(N+1) at hPres
  refine ⟨hTaylorActual.1,hTaylorActual.2.1,hTaylorActual.2.2.1,hTaylorActual.2.2.2.1,
    hPc,hPres,hTaylorActual.2.2.2.2.2.2.1,hTaylorActual.2.2.2.2.2.2.2,hQc.sub hPc,?_⟩
  have hhalf : (cQ/2)*delta*(tau : ℝ)/(tau : ℝ)^N =
      (cQ*delta*(tau : ℝ)/(tau : ℝ)^N)/2 := by ring
  rw [hhalf] at habs ⊢
  linarith

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_OriginalClassComparisonWithLow
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor SmoothLocal.Model

theorem exists_original_class_comparison_with_low_data
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∃ G d r : ℝ, 0 < G ∧ 0 < d ∧ 0 < r ∧ r < 1/2 ∧
      (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      (∀ a : ℝ, 0 < a → ∀ N : ℕ, 10 < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop,
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            (∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) ∧
            (∀ p ∈ modelSquare, d ≤ |(gTau p).det|)) ∧
      boundedClassWidth kappa M*r ≤ 1/20 ∧
      heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
        (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M) ∧
      (∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 10 < N → ∀ delta : ℝ, 0 < delta →
        ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
              1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            ∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 → ∀ n ≤ K,
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (-delta/(tau : ℝ))) x‖ ≤ B) ∧
              (‖iteratedFDeriv ℝ n (heightCauchyValue (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B ∧
              ‖iteratedFDeriv ℝ n (heightCauchyVelocity (heightInShearCoordinates z q0)
                (delta/(tau : ℝ))) x‖ ≤ B)) ∧
      ∀ N : ℕ, 10 < N → ∃ C Csource Cgradient c3 : ℝ,
        0 ≤ C ∧ 0 < Csource ∧ 0 ≤ Cgradient ∧ 0 < c3 ∧
        (∀ K : ℕ, ∃ CP : ℝ, 0 ≤ CP ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
            ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
              BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
              |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
              (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                  testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                    metricApproximationAccuracy tau) →
              let zs := heightInShearCoordinates z q0
              let gs := metricInShearCoordinates gStar q0
              let P := taylorApproximation gs (-delta/(tau : ℝ))
                (heightCauchyValue zs (-delta/(tau : ℝ)))
                (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
              ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
              (∀ j ≤ K, ∀ p : Coord, |p 0| ≤ boundedClassWidth kappa M*r/2 →
                |p 1| ≤ delta/(tau : ℝ) → ‖iteratedFDeriv ℝ j P p‖ ≤ CP) ∧
              CoordinateBound P (pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ)) K CP) ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ 1/2 → ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤ 1/(100*boundedClassWidth kappa M) →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) →
            let zs := heightInShearCoordinates z q0
            let gs := metricInShearCoordinates gStar q0
            let P := taylorApproximation gs (-delta/(tau : ℝ))
              (heightCauchyValue zs (-delta/(tau : ℝ)))
              (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
            ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r))) ∧
            (∀ x ∈ Ioo (-(boundedClassWidth kappa M*r)) (boundedClassWidth kappa M*r),
              P ![x,-delta/(tau : ℝ)] = zs ![x,-delta/(tau : ℝ)] ∧
              coordPartial 1 P ![x,-delta/(tau : ℝ)] = coordPartial 1 zs ![x,-delta/(tau : ℝ)]) ∧
            (∀ x, ∃ poly : Polynomial ℝ, poly.natDegree ≤ N+1 ∧ ∀ t, poly.eval t = P ![x,t]) ∧
            (∀ x : ℝ, |x| ≤ boundedClassWidth kappa M*r/2 →
              ∀ t ∈ Icc (-delta/(tau : ℝ)) (delta/(tau : ℝ)),
                (boundedClassSpeed kappa M)^2/(8*(M : ℝ)) ≤ |covHessian gs P ![x,t] 0 0| ∧
                |qResidual gs P ![x,t]| ≤ C/(tau : ℝ)^N) ∧
            ContinuousOn (qResidual gs P) (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ) (qResidual gs P)| ≤
              (2*C*(∫ x : ℝ, axisBump (boundedClassWidth kappa M*r/16) x))*delta/(tau : ℝ)^(N+1) ∧
            (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
              |actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P p| ≤
                Csource*(tau : ℝ)^2/(tau : ℝ)^N) ∧
            (∀ theta ∈ Icc (-(delta/(tau : ℝ))) (delta/(tau : ℝ)), ∀ i : Fin 2,
              Real.sqrt (∫ x in Icc (-(boundedClassWidth kappa M*r/16)) (boundedClassWidth kappa M*r/16),
                (coordPartial i (comparisonDifference P zs) (boxPoint x theta))^2) ≤
                Cgradient*delta*(tau : ℝ)/(tau : ℝ)^N) ∧
            ContinuousOn (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)
              (pulseStrip (boundedClassWidth kappa M*r/16) delta (tau : ℝ)) ∧
            c3*delta*(tau : ℝ)/(tau : ℝ)^N ≤
              |pulseWeightedMoment (boundedClassWidth kappa M*r/16) delta (tau : ℝ)
                (actualComparisonSource gStar (perturbedMetric g0 eta.val) z q0 P)| := by
  obtain ⟨G,d,hG,hd,hGstar,hdstar,hlow,hcuts⟩ :=
    exists_actual_class_two_sided_cauchy_bounds_at_every_radius
      hg0 hgStar hV hSV M hkappa hM hq0 hbackground
  have hGstar2 : ∀ i j : Fin 2, ∀ k ≤ 2, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G :=
    fun i j k hk p hp => hGstar i j k (by omega) p hp
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hcomparison⟩ :=
    exists_actual_class_comparison_moment hgStar hV hSV M hG.le hd hGstar2 hdstar hkappa hM hq0
  refine ⟨G,d,r,hG,hd,hr,hrhalf,hGstar,hdstar,hlow,hLr,hrsmall,
    hcuts r hr hrhalf hLr hrsmall,?_⟩
  intro N hN
  obtain ⟨C,Csource,Cgradient,c3,hC,hCs,hCg,hc3,hcomparisonN⟩ := hcomparison N (by omega)
  refine ⟨C,Csource,Cgradient,c3,hC,hCs,hCg,hc3,?_,?_⟩
  · intro K
    obtain ⟨CP,hCP,hPjets⟩ := exists_actual_taylor_finite_jets_at_radius
      hgStar hV hSV M hG.le hd hkappa hM hq0 hr hrhalf hLr hrsmall N K
    refine ⟨CP,hCP,?_⟩
    intro delta hdelt hdhalf
    have ha : 0 < boundedClassWidth kappa M*r/16 :=
      div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
    filter_upwards [hPjets delta hdelt hdhalf,
      hlow (boundedClassWidth kappa M*r/16) ha N hN delta] with tau hPjetsTau hlowTau
    intro eta z hclass hcenter happ
    obtain ⟨U,hU,hSU,hUV,_,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
    obtain ⟨hg8,hdet⟩ := hlowTau (perturbedMetric g0 eta.val) U hgU hU hSU happ
    have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G :=
      fun i j k hk p hp => hg8 i j k (by omega) p hp
    have hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p :=
      fun p hp => hbackground p (hUV hp)
    have hc : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
    obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
      hd hc hc hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
    exact hPjetsTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ
  intro delta hdelt hdhalf
  have ha : 0 < boundedClassWidth kappa M*r/16 := by
    exact div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)
  filter_upwards [hcomparisonN delta hdelt hdhalf,
    hlow (boundedClassWidth kappa M*r/16) ha N hN delta] with tau hcTau hlowTau
  intro eta z hclass hcenter happ
  obtain ⟨U,hU,hSU,hUV,_,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
  obtain ⟨hg8,hdet⟩ := hlowTau (perturbedMetric g0 eta.val) U hgU hU hSU happ
  have hg4 : ∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G :=
    fun i j k hk p hp => hg8 i j k (by omega) p hp
  have hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p :=
    fun p hp => hbackground p (hUV hp)
  have hc : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
    hd hc hc hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
  exact hcTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_OriginalPulseExclusion
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor SmoothLocal.Model

theorem exists_original_pulse_exclusion
    {g0 gStar : MetricField} {V : Set Coord}
    (hg0 : SmoothPositiveOn g0 V) (hgStar : SmoothPositiveOn gStar V)
    (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {kappa q0 : ℝ} (M : ℕ) (hkappa : 0 < kappa) (hM : 0 < M)
    (hq0 : |q0| ≤ 1/20)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ boundedClassWidth kappa M*r ≤ 1/20 ∧
      ∀ N : ℕ, 10 < N → ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1/2 ∧
        ∀ᶠ tau : ℕ in atTop,
          ∀ (eta : metricPatchSet g0 kappa) (z : Coord → ℝ),
            BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z →
            |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
              1/(100*boundedClassWidth kappa M) →
            ¬ (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j-
                testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                  metricApproximationAccuracy tau) := by
  obtain ⟨G,d,r,hG,hd,hr,hrhalf,hGstar,hdstar,hlow,hLr,hrsmall,hcuts,hcomparison⟩ :=
    exists_original_class_comparison_with_low_data hg0 hgStar hV hSV M hkappa hM hq0 hbackground
  have hGstar2 : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G :=
    fun i j k hk p hp => hGstar i j k (by omega) p hp
  let L := boundedClassWidth kappa M
  let a := L*r/16
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hLrpos : 0 < L*r := mul_pos hL hr
  have ha : 0 < a := div_pos hLrpos (by norm_num)
  have haHalf : a ≤ L*r/2 := by dsimp only [a] <;> linarith
  have haI : a < L*r := by dsimp only [a] <;> linarith
  have hminv : 0 < 1/(M : ℝ) := one_div_pos.mpr (Nat.cast_pos.mpr hM)
  have hxxfloor : 0 < (boundedClassSpeed kappa M)^2/(4*(M : ℝ)) :=
    div_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM)) (mul_pos (by norm_num) (Nat.cast_pos.mpr hM))
  refine ⟨r,hr,hrhalf,hLr,?_⟩
  intro N hN
  obtain ⟨C,Csource,Cgradient,c3,_hC,_hCsource,hCgradient,hc3,hPfinite,hcomparisonN⟩ := hcomparison N hN
  obtain ⟨K,K1,hK,hK1,hcoefficients⟩ := exists_actual_comparison_coefficient_data_at_radius
    hgStar hV hSV M hG.le hd hGstar2 hdstar hkappa hM hq0 hr hrhalf hLr hrsmall N (by omega)
  obtain ⟨CPseg,Aseg,_hCPseg,_hAseg,hsegments⟩ := exists_actual_reference_segment_at_radius
    hgStar hV hSV M hG.le hd hGstar2 hdstar hkappa hM hq0 hr hrhalf hLr hrsmall N (by omega)
  obtain ⟨BZ,hBZ,hZcuts⟩ := hcuts N
  obtain ⟨BP,hBP,hPjets⟩ := hPfinite (N+1)
  let E := (2*a)*cutoffEdgeDerivativeBound a ha N (BZ+BP)
  let C0 := 4*pulseTestDerivativeBound a ha*K*Real.sqrt (2*a)*Cgradient
  let C1 := 4*axisBumpDerivativeBound a ha 0*(K1+K)*Real.sqrt (2*a)*Cgradient
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hC0 : 0 ≤ C0 := by
    dsimp only [C0]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (pulseTestDerivativeBound_nonneg ha)) hK0) (Real.sqrt_nonneg _)) hCgradient
  obtain ⟨delta,hdelt,hdhalf,hcontradict⟩ := exists_delta_then_frequency_for_moment_contradiction hc3 hC0 N
  obtain ⟨T,_hT,hcontradictT⟩ := hcontradict E C1
  refine ⟨delta,hdelt,hdhalf,?_⟩
  have hlarge : ∀ᶠ tau : ℕ in atTop, T ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop T)
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [hcomparisonN delta hdelt hdhalf,hlow a ha N hN delta,
    hZcuts N hN delta hdelt,hPjets delta hdelt hdhalf,hcoefficients delta hdelt hdhalf,
    hsegments delta hdelt hdhalf,hlarge,hwidth]
    with tau hcomparisonTau hlowTau hZcutsTau hPjetsTau hcoeffTau hsegmentsTau ht hw
  intro eta z hclass hcenter happ
  let g := perturbedMetric g0 eta.val
  obtain ⟨U,hU,hSU,hUV,_hg0U,hgU,hh⟩ := bounded_class_actual_cap_data hg0 hV hSV eta hclass
  obtain ⟨hg8,hdet⟩ := hlowTau g U hgU hU hSU happ
  have hg4 : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G := fun i j k hk p hp => hg8 i j k (by omega) p hp
  have hmodel : ∀ p ∈ U, gaussianCurvature g0 p=modelCurvature kappa p := fun p hp => hbackground p (hUV hp)
  obtain ⟨W,Y,hf⟩ := exists_capInductionFlow hgU hU hSU hG.le (Nat.cast_nonneg M)
    hd hminv hminv hg8 hdet hh hkappa hmodel (perturbationTensor_tsupport_subset eta.val) eta.property.2
  let zs := heightInShearCoordinates z q0
  let gs := metricInShearCoordinates gStar q0
  let gt := metricInShearCoordinates g q0
  let P := taylorApproximation gs (-delta/(tau : ℝ))
    (heightCauchyValue zs (-delta/(tau : ℝ))) (heightCauchyVelocity zs (-delta/(tau : ℝ))) N
  let I := Ioo (-(L*r)) (L*r)
  let Us := inverseShearCoordinates q0 ⁻¹' U
  let D := Us ∩ spatialStrip I
  let S := pulseStrip a delta (tau : ℝ)
  have hUs : IsOpen Us := shearedModelDomain_isOpen hU q0
  have hD : IsOpen D := hUs.inter (spatialStrip_isOpen isOpen_Ioo)
  have htpos : (0 : ℝ) < tau := zero_lt_one.trans_le hw.1
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have htime0 : 0 ≤ delta/(tau : ℝ) := div_nonneg hdelt.le htpos.le
  have hpointEq (x t : ℝ) : boxPoint x t = (![x,t] : Coord) := pulse_boxPoint_eq x t
  have hsubset : S ⊆ pulseStrip (L*r/2) delta (tau : ℝ) := by
    intro p hp
    exact ⟨⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩,hp.2⟩
  have hcoordinates (p : Coord) (hp : p ∈ S) : |p 0| ≤ L*r ∧ |p 1| ≤ r :=
    ⟨(abs_le.mpr hp.1).trans haI.le,(abs_le.mpr hp.2).trans hbr⟩
  have hgeom (p : Coord) (hp : p ∈ S) := actual_central_sheared_solution_margins
    eta hclass hG.le hd hkappa hr.le hLr hq0 hrsmall hg4 hdet hcenter
      (hcoordinates p hp).1 (hcoordinates p hp).2
  have hpS (p : Coord) (hp : p ∈ S) : inverseShearCoordinates q0 p ∈ modelSquare := (hgeom p hp).1
  have hSD : S ⊆ D := by
    intro p hp
    exact ⟨hSU (hpS p hp),⟨by linarith [hp.1.1],by linarith [hp.1.2]⟩⟩
  have hgStarU : SmoothPositiveOn gStar U :=
    ⟨fun i j => (hgStar.1 i j).mono hUV,fun p hp => hgStar.2 p (hUV hp)⟩
  have hgsUs := metricInShearCoordinates_smoothPositive hgStarU q0
  have hgtUs := metricInShearCoordinates_smoothPositive hgU q0
  have hgsD : SmoothPositiveOn gs D :=
    ⟨fun i j => (hgsUs.1 i j).mono inter_subset_left,fun p hp => hgsUs.2 p hp.1⟩
  have hgtD : SmoothPositiveOn gt D :=
    ⟨fun i j => (hgtUs.1 i j).mono inter_subset_left,fun p hp => hgtUs.2 p hp.1⟩
  have hzsUs := heightInShearCoordinates_contDiffOn hh.smooth q0
  have hzsD : ContDiffOn ℝ ∞ zs D := hzsUs.mono inter_subset_left
  obtain ⟨hP,hCauchy,_hdegree,_hres,_hresc,_hresm,_hsource,hgradient,_hsourcec,hpositive⟩ :=
    hcomparisonTau eta z hclass hcenter happ
  have hPD : ContDiffOn ℝ ∞ P D := hP.mono inter_subset_right
  have hcoeff := hcoeffTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ
  have hsegments := (hsegmentsTau g0 eta U W z Y hgU hU hh hf hclass hg4 hdet hcenter happ).2.2
  have hseg (p : Coord) (hp : p ∈ S) (sigma : ℝ) (hsigma : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P zs sigma p ∈ darbouxQStateDomain gs D := by
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hSD hp,
      abs_pos.mp (hxxfloor.trans_le (hsegments p (hsubset hp) sigma hsigma).1)⟩
  have hcut (x : ℝ) (hx : x ∈ I) (t : ℝ) (ht : |t| ≤ r) : (![x,t] : Coord) ∈ D := by
    refine ⟨hSU ?_,hx⟩
    apply sectionFourClosedSlab_mem_shearedModelSquare hr hrhalf hLr hq0
    exact ⟨abs_le.mpr ⟨hx.1.le,hx.2.le⟩,ht⟩
  have hinitial (x : ℝ) (hx : x ∈ Icc (-a) a) :
      coordPartial 1 (comparisonDifference P zs) (boxPoint x (-(delta/(tau : ℝ))))=0 := by
    have hxI : x ∈ I := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have ht0 : |-(delta/(tau : ℝ))| ≤ r := by rw [abs_neg,abs_of_nonneg htime0]; exact hbr
    have hpD : boxPoint x (-(delta/(tau : ℝ))) ∈ D := by rw [hpointEq]; exact hcut x hxI _ ht0
    have hs := CoordinateBound.iterated_sub hzsD hPD hD [1] hpD
    change coordPartial 1 (comparisonDifference P zs) (boxPoint x (-(delta/(tau : ℝ)))) =
      coordPartial 1 zs (boxPoint x (-(delta/(tau : ℝ))))-
        coordPartial 1 P (boxPoint x (-(delta/(tau : ℝ)))) at hs
    have he := (hCauchy x hxI).2
    change coordPartial 1 P ![x,-delta/(tau : ℝ)] =
      coordPartial 1 zs ![x,-delta/(tau : ℝ)] at he
    rw [neg_div] at he
    rw [hpointEq,he,sub_self] at hs
    simpa only [hpointEq] using hs
  have hPjetsActual := hPjetsTau eta z hclass hcenter happ
  have hZcutsActual := hZcutsTau eta z hclass hcenter happ
  have hedge (n : ℕ) (hn : n ≤ N) (x : ℝ) (hx : x ∈ Icc (-a) a) :
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity (comparisonDifference P zs) (delta/(tau : ℝ))) x‖ ≤ BZ+BP := by
    have hxI : x ∈ I := ⟨by linarith [hx.1],by linarith [hx.2]⟩
    have hxhalf : |x| ≤ L*r/2 := (abs_le.mpr hx).trans haHalf
    have hPcut := upper_cauchy_jets_of_actual_coordinate_bound hPjetsActual.1
      (show L*r/2<L*r by linarith) htime0 hPjetsActual.2.2 hxhalf n hn
    have hzcut := (hZcutsActual x hxhalf n hn).2.2
    apply comparison_upper_velocity_jet_bound hD isOpen_Ioo hPD hzsD (delta/(tau : ℝ))
      (fun y hy => hcut y hy _ (by rw [abs_of_nonneg htime0]; exact hbr)) hxI n hzcut hPcut.2
  have hcost := actual_comparison_source_test_cost ha hdelt.le hw.1 hK0 hK1 hCgradient
    (add_nonneg hBZ hBP) hgtD hgsD hD hzsD hPD hSD
    (fun p hp => (hgeom p hp).2.2.2.2.2.1)
    (fun p hp => abs_pos.mp ((boundedClassShearHxxFloor_pos hkappa hM).trans_le (hgeom p hp).2.1))
    hseg (fun i p hp => (hcoeff i p (hsubset hp)).1)
    (fun i p hp => (hcoeff i p (hsubset hp)).2) hgradient hinitial hedge
  change |pulseWeightedMoment a delta (tau : ℝ) (actualComparisonSource gStar g z q0 P)| ≤
    E/(tau : ℝ)^N+C0*delta^2*(tau : ℝ)/(tau : ℝ)^N+C1*delta^2/(tau : ℝ)^N at hcost
  exact hcontradictT (tau : ℝ) ht
    (pulseWeightedMoment a delta (tau : ℝ) (actualComparisonSource gStar g z q0 P)) hpositive hcost

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_BoundedClassNowhereDense
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Flow SmoothLocal.Model

theorem boundedHeightClass_isNowhereDense
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    (M : ℕ) (q0 : ℚ) :
    IsNowhereDense (boundedHeightClass g0 kappa M q0) := by
  change interior (closure (boundedHeightClass g0 kappa M q0)) = ∅
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro etaStar hStar
  let O := interior (closure (boundedHeightClass g0 kappa M q0))
  have hO : IsOpen O := isOpen_interior
  have hOclosure : O ⊆ closure (boundedHeightClass g0 kappa M q0) := interior_subset
  have hparameters := boundedHeightClass_closure_parameters (hOclosure hStar)
  have hgStar : SmoothPositiveOn (perturbedMetric g0 etaStar.val) V :=
    perturbedMetric_smoothPositiveOn hg0 etaStar.val etaStar.property.1
  obtain ⟨r,hr,_,hLr,hexclusion⟩ := exists_original_pulse_exclusion
    hg0 hgStar hV hSV M hkappa hparameters.1 hparameters.2.le hbackground
  obtain ⟨N,hN,happroximants⟩ := bounded_class_open_closure_pulse_family_at_radius
    hg0 hV hSV M q0 hO hStar hOclosure hr hLr
  obtain ⟨delta,hdelt,_,hnoheight⟩ := hexclusion N hN
  obtain ⟨tau,happroxTau,hnoheightTau⟩ := ((happroximants delta hdelt).and hnoheight).exists
  obtain ⟨eta,z,hclass,hcenter,haccuracy⟩ := happroxTau.2
  exact hnoheightTau eta z hclass hcenter haccuracy

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_PatchResidualTheorem
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.assemblyProfileEncodable _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Model

theorem patchObstructionSet_dense
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p) :
    Dense (patchObstructionSet g0 kappa) := by
  let : BaireSpace (metricPatchSet g0 kappa) := metricPatchSet_baire hg0 hV hSV kappa
  change Dense (⋂ index : ℕ × ℚ, (closure (boundedHeightClass g0 kappa index.1 index.2))ᶜ)
  apply dense_iInter_of_isOpen (fun _ => isClosed_closure.isOpen_compl)
  intro index
  exact (isClosed_isNowhereDense_iff_compl.mp ⟨isClosed_closure,
    (boundedHeightClass_isNowhereDense hg0 hV hSV hkappa hbackground index.1 index.2).closure⟩).2

theorem exists_patch_obstruction_in_open
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    {O : Set (metricPatchSet g0 kappa)} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ eta ∈ O,
      SmoothPositiveOn (perturbedMetric g0 eta.val) V ∧
      (∀ p ∈ centralBox, gaussianCurvature (perturbedMetric g0 eta.val) p < -kappa/2) ∧
      ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta.val) z := by
  obtain ⟨eta,hetaGood,hetaO⟩ :=
    (patchObstructionSet_dense hg0 hV hSV hkappa hbackground).exists_mem_open hO hne
  exact ⟨eta,hetaO,perturbedMetric_smoothPositiveOn hg0 eta.val eta.property.1,
    eta.property.2,patchObstructionSet_has_no_admissible_height hetaGood⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_SmallPatchObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Model

theorem exists_supported_patch_obstruction_in_open
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p)
    {O : Set SymmetricPerturbation} (hO : IsOpen O) (hzero : (0 : SymmetricPerturbation) ∈ O) :
    ∃ eta : SymmetricPerturbation, eta ∈ O ∧ eta ∈ metricPatchSet g0 kappa ∧
      SmoothPositiveOn (perturbedMetric g0 eta) V ∧
      ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta) z := by
  let zeroPatch : metricPatchSet g0 kappa :=
    ⟨0,model_zero_mem_metricPatchSet hg0 hSV hkappa hbackground⟩
  let W : Set (metricPatchSet g0 kappa) := Subtype.val ⁻¹' O
  have hW : IsOpen W := hO.preimage continuous_subtype_val
  have hWzero : zeroPatch ∈ W := hzero
  obtain ⟨eta,hetaW,hg,_,hno⟩ :=
    exists_patch_obstruction_in_open hg0 hV hSV hkappa hbackground hW ⟨zeroPatch,hWzero⟩
  exact ⟨eta.val,hetaW,eta.property,hg,hno⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_SelectedPatchObstructions
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

theorem exists_obstructing_patch_tensor (a : PatchAddress) :
    ∃ eta : SymmetricPerturbation,
      eta ∈ patchTensorBudgetNeighborhood 1 a ∧
      eta ∈ metricPatchSet (patchAddressInitialMetric a) (patchAddressAmplitude a) ∧
      SmoothPositiveOn (perturbedMetric (patchAddressInitialMetric a) eta) patchAddressModelDomain ∧
      ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric (patchAddressInitialMetric a) eta) z :=
  exists_supported_patch_obstruction_in_open (patchAddressInitialMetric_smoothPositive a)
    patchAddressModelDomain_isOpen modelSquare_subset_patchAddressModelDomain
    (patchAddressAmplitude_pos a) (fun p hp => patchAddressInitialMetric_curvature a hp)
    (patchTensorBudgetNeighborhood_isOpen 1 a)
    (zero_mem_patchTensorBudgetNeighborhood (by norm_num : (0 : ℝ) < 1) a)

def selectedPatchTensor (a : PatchAddress) : SymmetricPerturbation :=
  Classical.choose (exists_obstructing_patch_tensor a)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_FinalMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

def counterexampleMetric : MetricField :=
  assembledPatchMetric initialAssemblyMetric selectedPatchTensor

end SmoothLocal.Geometry

end

end OAI
end


