-- Prove2me | Definitions.Def_Q226II015
-- name    : Q226II015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:55:31.847233+00:00
-- url     : https://prove2.me/theorems/a12b3d52-e993-47ea-97a0-155237f5e27a
-- title:
--   Definitions bundle Q226II015 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 18 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`IsometricImmersion_Comparison_ComparisonPulseGeometry`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Comparison/ComparisonPulseGeometry.lean), [`IsometricImmersion_Darboux_QMetricFirstErrorBound`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Darboux/QMetricFirstErrorBound.lean), [`IsometricImmersion_Estimates_ActualQCompactBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Estimates/ActualQCompactBounds.lean), [`IsometricImmersion_Estimates_ActualQPointBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Estimates/ActualQPointBounds.lean), [`IsometricImmersion_Metrics_ActualLowMetricFloor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Metrics/ActualLowMetricFloor.lean), [`IsometricImmersion_Metrics_ActualTestMetricPositive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Metrics/ActualTestMetricPositive.lean), [`IsometricImmersion_Metrics_LocalMetricQActive`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Metrics/LocalMetricQActive.lean), [`IsometricImmersion_Pulses_PulseCurvaturePrincipal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Pulses/PulseCurvaturePrincipal.lean), [`IsometricImmersion_Pulses_PulseDensityGlobal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Pulses/PulseDensityGlobal.lean), [`IsometricImmersion_Pulses_PulseDensitySlab`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Pulses/PulseDensitySlab.lean).
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II011`, `Q226II012` and `Q226II013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II017` and `Q226II018`.
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
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
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
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Countable
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
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
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II011
import Definitions.Def_Q226II012
import Definitions.Def_Q226II013

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseCurvaturePrincipal
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem thetaPulse_curvature_density {g : MetricField} {f : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hplus : SmoothPositiveOn (thetaPulseMetric g f) U)
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) :
    gaussianCurvature (thetaPulseMetric g f) p*(thetaPulseMetric g f p).det -
      gaussianCurvature g p*(g p).det =
        -(1/2 : ℝ)*coordPartial 0 (coordPartial 0 f) p + thetaPulseLowerDifference g f p := by
  have h00 : (fun q => thetaPulseMetric g f q 0 0) = (fun q => g q 0 0) := by
    funext q
    simp [thetaPulseMetric_entry]
  have h01 : (fun q => thetaPulseMetric g f q 0 1) = (fun q => g q 0 1) := by
    funext q
    simp [thetaPulseMetric_entry]
  have h11 : (fun q => thetaPulseMetric g f q 1 1) = (fun q => g q 1 1+f q) := by
    funext q
    simp [thetaPulseMetric_entry]
  have hnew := gaussianCurvature_density_principal_part hplus hU hp
  rw [h00,h01,h11,secondCoordPartial_add (hg.1 1 1) hf hU hp 0 0] at hnew
  have hold := gaussianCurvature_density_principal_part hg hU hp
  rw [hnew,hold,thetaPulseLowerDifference_eq hg hf hU hp]
  ring

theorem actual_pulse_curvature_density
    {gStar : MetricField} {U : Set Coord} (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    (hg : SmoothPositiveOn gStar U)
    (htest : SmoothPositiveOn (testMetric gStar q0 a N delta tau) U)
    (hU : IsOpen U) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U) :
    gaussianCurvature (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p) *
        (testMetric gStar q0 a N delta tau (inverseShearCoordinates q0 p)).det -
      gaussianCurvature gStar (inverseShearCoordinates q0 p) *
        (gStar (inverseShearCoordinates q0 p)).det =
      -(1/2 : ℝ)*coordPartial 0 (coordPartial 0 (pulseScalar a N delta tau)) p +
        thetaPulseLowerDifference (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) p := by
  let R := inverseShearMatrix q0
  let V := affineCoordinates 0 R ⁻¹' U
  have hR : IsUnit R := inverseShearMatrix_isUnit q0
  have hV : IsOpen V := hU.preimage (affineCoordinates_contDiff 0 R).continuous
  have hpV : p ∈ V := by
    simpa only [V,R,Set.mem_preimage,←inverseShearCoordinates_eq_affine] using hp
  have hgV : SmoothPositiveOn (metricInShearCoordinates gStar q0) V :=
    affinePullbackMetric_smoothPositive hg 0 R (Matrix.mulVec_injective_of_isUnit hR)
  have htV : SmoothPositiveOn
      (metricInShearCoordinates (testMetric gStar q0 a N delta tau) q0) V :=
    affinePullbackMetric_smoothPositive htest 0 R (Matrix.mulVec_injective_of_isUnit hR)
  have htTheta : SmoothPositiveOn
      (thetaPulseMetric (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau)) V := by
    rw [←metricInShearCoordinates_test]
    exact htV
  have hformula := thetaPulse_curvature_density hgV htTheta
    (pulseScalar_contDiff a N delta tau).contDiffOn hV hpV
  rw [←metricInShearCoordinates_test] at hformula
  have hpa : affineCoordinates 0 R p ∈ U := hpV
  have hKg := gaussianCurvature_affinePullback hg hU 0 R hR p hpa
  have hKt := gaussianCurvature_affinePullback htest hU 0 R hR p hpa
  change gaussianCurvature (affinePullbackMetric (testMetric gStar q0 a N delta tau) 0 R) p *
      (affinePullbackMetric (testMetric gStar q0 a N delta tau) 0 R p).det -
      gaussianCurvature (affinePullbackMetric gStar 0 R) p *
        (affinePullbackMetric gStar 0 R p).det = _ at hformula
  rw [hKt,hKg,det_affinePullbackMetric,det_affinePullbackMetric] at hformula
  simpa only [R,inverseShearMatrix_det,one_pow,one_mul,
    ←inverseShearCoordinates_eq_affine] using hformula

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseDensitySlab
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem curvatureDensityJetError_eq {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) :
    curvatureDensityJetError g h p = curvatureDensity g p-curvatureDensity h p := by
  unfold curvatureDensity curvatureDensityJetError
  rw [gaussianCurvature_density_principal_part hg hU hp,
    gaussianCurvature_density_principal_part hh hU hp]
  ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QMetricFirstErrorBound
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

theorem exists_uniform_qMetricFirstError_bound (B D : ℝ) {d c : ℝ}
    (hD : 0 ≤ D) (hd : 0 < d) (hc : 0 < c) :
    ∃ H C : ℝ, 0 ≤ H ∧ 0 ≤ C ∧
      ∀ (gTau gStar : MetricField) (w : DarbouxState) (epsilon : ℝ),
        ‖qFirstBundle gStar w‖ ≤ B → d ≤ (gStar (statePoint w)).det →
        c ≤ |stateQDenominator gStar w| →
        ‖actualCurvatureFirstInput gTau (statePoint w)-
          actualCurvatureFirstInput gStar (statePoint w)‖ ≤ epsilon →
        epsilon ≤ 1 → (4*max B 0+2)*epsilon ≤ d/2 → H*epsilon ≤ c/2 →
        |curvatureDensity gTau (statePoint w)| ≤ D →
        c/2 ≤ |stateQDenominator gTau w| ∧
        |qMetricFirstError gTau gStar w| ≤ C*epsilon := by
  obtain ⟨H,F,L,hH,hF,hL,hcompare⟩ := exists_uniform_qFirst_comparison B hd hc
  refine ⟨H,D*F+L,hH,add_nonneg (mul_nonneg hD hF) hL,?_⟩
  intro gTau gStar w epsilon hB hdet hxx hdist he1 hsmall hxxsmall hdensity
  have hscale : 0 ≤ 4*max B 0+2 := by linarith [le_max_right B 0]
  have hb : ‖qFirstBundle gTau w-qFirstBundle gStar w‖ ≤ epsilon := by
    simpa only [qFirstBundle_distance] using hdist
  obtain ⟨hfloor,hfactor,hlower⟩ := hcompare (qFirstBundle gStar w) (qFirstBundle gTau w)
    hB hdet hxx (hb.trans he1)
    ((mul_le_mul_of_nonneg_left hb hscale).trans hsmall)
    ((mul_le_mul_of_nonneg_left hb hH).trans hxxsmall)
  have hxxTau : c/2 ≤ |stateQDenominator gTau w| := by
    simpa only [qFirstXX_bundle] using
      hfloor (qFirstBundle gTau w) (right_mem_segment ℝ _ _)
  have hfactorBase : |qMetricDensityFactor gTau w-qMetricDensityFactor gStar w| ≤
      F*‖qFirstBundle gTau w-qFirstBundle gStar w‖ := by
    simpa only [qFirstDensityFactor_bundle] using hfactor
  have hlowerBase : |qMetricFirstLower gTau w-qMetricFirstLower gStar w| ≤
      L*‖qFirstBundle gTau w-qFirstBundle gStar w‖ := by
    simpa only [qFirstLower_bundle] using hlower
  have hfactor' : |qMetricDensityFactor gTau w-qMetricDensityFactor gStar w| ≤ F*epsilon :=
    hfactorBase.trans (mul_le_mul_of_nonneg_left hb hF)
  have hlower' : |qMetricFirstLower gTau w-qMetricFirstLower gStar w| ≤ L*epsilon :=
    hlowerBase.trans (mul_le_mul_of_nonneg_left hb hL)
  refine ⟨hxxTau,?_⟩
  unfold qMetricFirstError
  calc
    _ ≤ |curvatureDensity gTau (statePoint w)| *
          |qMetricDensityFactor gTau w-qMetricDensityFactor gStar w|+
        |qMetricFirstLower gTau w-qMetricFirstLower gStar w| := by
      simpa only [abs_mul] using abs_add_le
        (curvatureDensity gTau (statePoint w)*(qMetricDensityFactor gTau w-qMetricDensityFactor gStar w))
        (qMetricFirstLower gTau w-qMetricFirstLower gStar w)
    _ ≤ D*(F*epsilon)+L*epsilon := add_le_add
      (mul_le_mul hdensity hfactor' (abs_nonneg _) hD) hlower'
    _ = _ := by ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseDensityGlobal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem exists_test_density_global_bound (B : ℝ) {d : ℝ} (hd : 0 < d)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
      ∀ tau : ℝ, T ≤ tau → ∀ (gStar : MetricField) (q0 : ℝ) (U : Set Coord),
        SmoothPositiveOn gStar U → SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
        IsOpen U → ∀ p : Coord, inverseShearCoordinates q0 p ∈ U →
          ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ B →
          d ≤ (metricInShearCoordinates gStar q0 p).det →
          |(curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
              curvatureDensity gStar (inverseShearCoordinates q0 p))-
            pulsePrincipalLeading a N delta tau p| ≤
            testDensityErrorCoefficient C a ha delta*tau/tau^N := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_actual_pulse_lower_bound B hd ha N hN
  refine ⟨C,hC,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hsmall⟩ := hbound delta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar q0 U hg htest hU p hpU hjet hdet
  have ht1 : 1 ≤ tau := hT.trans ht
  have hL := hsmall tau ht (metricInShearCoordinates gStar q0) p hjet hdet
  have hR := pulse_principal_remainder_le ha N delta ht1 p
  have heq := actual_pulse_curvature_density q0 a N delta tau hg htest hU hpU
  rw [pulse_principal_exact] at heq
  have hdensity :
      (curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-pulsePrincipalLeading a N delta tau p =
        pulsePrincipalRemainder a N delta tau p+
          thetaPulseLowerDifference (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) p := by
    dsimp only [curvatureDensity]
    linarith only [heq]
  rw [hdensity]
  calc
    _ ≤ |pulsePrincipalRemainder a N delta tau p|+
        |thetaPulseLowerDifference (metricInShearCoordinates gStar q0) (pulseScalar a N delta tau) p| :=
      abs_add_le _ _
    _ ≤ pulsePrincipalRemainderBound a ha*tau/tau^N+
        C*scalarPulseFirstJetBudget a ha N delta tau := add_le_add hR hL
    _ = _ := by unfold testDensityErrorCoefficient scalarPulseFirstJetBudget; ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_LocalMetricQActive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem actual_fixedTime_Q_jet_bound_from_universalTube
    {g : MetricField} {U : Set Coord} {theta : ℝ} {v : QSpatialState}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hv : v ∈ qFixedTimeDomain g U theta)
    {N : ℕ} {G W d c C : ℝ} (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgB : HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G)
    (hwB : ‖qFixedTimeState theta v‖ ≤ W)
    (hdet : d ≤ |(g (coordinatePoint (v 0) theta)).det|)
    (hden : c ≤ |stateQDenominator g (qFixedTimeState theta v)|)
    (hC : ∀ k ≤ N, ∀ a ∈ universalMetricQTube (max G W) d c,
      ‖iteratedFDeriv ℝ k universalMetricQ a‖ ≤ C)
    {n : ℕ} (hn : n ≤ N) :
    ‖iteratedFDeriv ℝ n (qFixedTimeQ g theta) v‖ ≤ n.factorial * C * (max 1 G)^n := by
  have hD := qFixedTimeDomain_isOpen hg hU theta
  have hsub : qFixedTimeDomain g U theta ⊆ qFixedTimeBaseDomain U theta := by
    intro w hw
    simpa only [statePoint_qFixedTimeState, qFixedTimeBaseDomain, Set.mem_ofPred_eq] using hw.1
  have hf := (metricQSpatialBundle_contDiffOn hg hU theta).mono hsub
  have hmap := metricQSpatialBundle_mapsTo_domain hg theta
  have hmem : metricQSpatialBundle g theta v ∈ universalMetricQTube (max G W) d c := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [Metric.mem_closedBall, dist_zero_right] using metricQSpatialBundle_norm_bound hG hgB hwB
    · simpa only [metricQSpatialBundle, Function.comp_apply, metricPBundle, statePoint_qFixedTimeState,
        Set.mem_preimage, Set.mem_Ici] using hdet
    · simpa only [Set.mem_preimage, Set.mem_ofPred_eq, metricQSpatialBundle,
        Function.comp_apply, universalQDenominator_metricPBundle] using hden
  have ho : ∀ i, i ≤ n →
      ‖iteratedFDerivWithin ℝ i universalMetricQ universalMetricQDomain (metricQSpatialBundle g theta v)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i universalMetricQDomain_isOpen
      (universalMetricQTube_subset_domain (max G W) hd hc hmem)]
    exact hC i (hi.trans hn) _ hmem
  have hi : ∀ i, 1 ≤ i → i ≤ n →
      ‖iteratedFDerivWithin ℝ i (metricQSpatialBundle g theta) (qFixedTimeDomain g U theta) v‖ ≤ (max 1 G)^i := by
    intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hD hv]
    exact (metricQSpatialBundle_positive_jet_bound hg hU (hsub hv) hG hgB hi (hin.trans hn)).trans
      (le_self_pow₀ (le_max_left _ _) (by omega))
  have hcomp := norm_iteratedFDerivWithin_comp_le universalMetricQ_contDiffOn hf
    (WithTop.coe_le_coe.mpr le_top) universalMetricQDomain_isOpen.uniqueDiffOn hD.uniqueDiffOn
    hmap hv ho hi
  have heq : iteratedFDerivWithin ℝ n (qFixedTimeQ g theta) (qFixedTimeDomain g U theta) v =
      iteratedFDerivWithin ℝ n (universalMetricQ ∘ metricQSpatialBundle g theta) (qFixedTimeDomain g U theta) v :=
    iteratedFDerivWithin_congr
      (fun w hw => sixVariableQ_eq_universalMetricQ hg hU hw.1) hv n
  rw [iteratedFDerivWithin_of_isOpen n hD hv] at heq
  rw [← heq] at hcomp
  exact hcomp

theorem exists_local_fixedTime_Q_jet_bound (G W : ℝ) (hG : 0 ≤ G)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ (theta : ℝ) (v : QSpatialState),
      coordinatePoint (v 0) theta ∈ U →
      HorizontalMetricTwoJetBound g (coordinatePoint (v 0) theta) N G →
      ‖qFixedTimeState theta v‖ ≤ W →
      d ≤ |(g (coordinatePoint (v 0) theta)).det| →
      c ≤ |stateQDenominator g (qFixedTimeState theta v)| →
      ∀ n ≤ N, ‖iteratedFDeriv ℝ n (qFixedTimeQ g theta) v‖ ≤ C := by
  classical
  obtain ⟨C0, hC0, hCQ⟩ := universalMetricQTube_finite_bounds (max G W) hd hc N
  let C : ℝ := ∑ k : Fin (N + 1), (k.val.factorial : ℝ) * C0 * (max 1 G)^k.val
  have hC : 0 ≤ C := Finset.sum_nonneg (fun k _ => by positivity)
  refine ⟨C, hC, ?_⟩
  intro g U hg hU theta v hp hgB hwB hdet hden n hn
  have hne : stateQDenominator g (qFixedTimeState theta v) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hden
    linarith
  have hv : v ∈ qFixedTimeDomain g U theta :=
    ⟨by simpa only [statePoint_qFixedTimeState] using hp, hne⟩
  have hb := actual_fixedTime_Q_jet_bound_from_universalTube hg hU hv hG hd hc hgB hwB hdet hden hCQ hn
  let j : Fin (N + 1) := ⟨n, by omega⟩
  have hsum : (j.val.factorial : ℝ) * C0 * (max 1 G)^j.val ≤
      ∑ i : Fin (N+1), (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val :=
    Finset.single_le_sum
      (f := fun i : Fin (N+1) => (i.val.factorial : ℝ) * C0 * (max 1 G)^i.val)
      (fun i _ => by positivity) (Finset.mem_univ j)
  exact hb.trans hsum

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonPulseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem pulseStrip_subset_comparisonSlab
    {a delta tau speed : ℝ} (_ha : 0 ≤ a) (_hd : 0 ≤ delta) (_ht : 0 < tau)
    (hs : 0 ≤ speed) (htravel : speed*(2*delta/tau) ≤ 3*a) :
    pulseStrip a delta tau ⊆ shrinkingSlab (-(4*a)) (4*a) (-(delta/tau)) (delta/tau) speed := by
  intro p hp
  have hpT : p 1 ∈ Icc (-(delta/tau)) (delta/tau) := hp.2
  have hm : speed*(p 1-(-(delta/tau))) ≤ speed*(2*delta/tau) := by
    apply mul_le_mul_of_nonneg_left _ hs
    calc
      _ ≤ delta/tau+delta/tau := by linarith [hpT.2]
      _ = _ := by ring
  refine ⟨hpT,?_⟩
  change -(4*a)+speed*(p 1-(-(delta/tau))) ≤ p 0 ∧
    p 0 ≤ 4*a-speed*(p 1-(-(delta/tau)))
  constructor <;> linarith [hp.1.1,hp.1.2]

theorem comparisonSlab_subset_dataStrip
    {a delta tau speed : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ speed) :
    shrinkingSlab (-(4*a)) (4*a) (-(delta/tau)) (delta/tau) speed ⊆
      pulseStrip (8*a) delta tau := by
  intro p hp
  have hinc : 0 ≤ speed*(p 1-(-(delta/tau))) := mul_nonneg hs (sub_nonneg.mpr hp.1.1)
  refine ⟨?_,hp.1⟩
  change -(8*a) ≤ p 0 ∧ p 0 ≤ 8*a
  change p 1 ∈ Icc (-(delta/tau)) (delta/tau) ∧
    (-(4*a)+speed*(p 1-(-(delta/tau))) ≤ p 0 ∧
      p 0 ≤ 4*a-speed*(p 1-(-(delta/tau)))) at hp
  constructor <;> linarith [hp.2.1,hp.2.2]

theorem comparison_pulse_geometry_eventually
    {a speed : ℝ} (ha : 0 < a) (hs : 0 ≤ speed) (delta : ℝ) (hd : 0 ≤ delta) :
    ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧
      speed*(2*delta/(tau : ℝ)) ≤ 3*a ∧
      pulseStrip a delta (tau : ℝ) ⊆
        shrinkingSlab (-(4*a)) (4*a) (-(delta/(tau : ℝ))) (delta/(tau : ℝ)) speed ∧
      shrinkingSlab (-(4*a)) (4*a) (-(delta/(tau : ℝ))) (delta/(tau : ℝ)) speed ⊆
        pulseStrip (8*a) delta (tau : ℝ) := by
  have hlarge : ∀ᶠ tau : ℕ in atTop, max 1 (2*speed*delta/(3*a)) ≤ (tau : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop _)
  filter_upwards [hlarge] with tau htau
  have ht1 : 1 ≤ (tau : ℝ) := (le_max_left _ _).trans htau
  have ht : (0 : ℝ) < tau := zero_lt_one.trans_le ht1
  have htravel := comparison_pulse_travel_bound ha ht ((le_max_right _ _).trans htau)
  exact ⟨ht1,htravel,pulseStrip_subset_comparisonSlab ha.le hd ht hs htravel,
    comparisonSlab_subset_dataStrip ha.le hs⟩

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualQCompactBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem exists_actual_forcingCoefficient_bound (B : ℝ) {d c : ℝ}
    (hd : 0 < d) (hc : 0 < c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U : Set Coord),
      SmoothPositiveOn g U → ∀ p ∈ U,
      ‖qFirstBundle g (qSolutionJet z p)‖ ≤ B → d ≤ (g p).det →
      c ≤ |covHessian g z p 0 0| → |forcingCoefficient g z p| ≤ A := by
  obtain ⟨A,hA⟩ := (qFirstTube_isCompact B hd c).exists_bound_of_continuousOn
    (qFirstDensityFactor_contDiffOn.continuousOn.mono (qFirstTube_subset_domain B hd hc))
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro g z U hg p hp hB hdet hxx
  have hin : qFirstBundle g (qSolutionJet z p) ∈ qFirstTube B d c := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using hB
    · change d ≤ qFirstDet (qFirstBundle g (qSolutionJet z p))
      simpa only [qFirstDet_bundle,statePoint_qSolutionJet] using hdet
    · change c ≤ |qFirstXX (qFirstBundle g (qSolutionJet z p))|
      simpa only [qFirstXX_bundle,stateQDenominator_qSolutionJet] using hxx
  have hne := abs_pos.mp (hc.trans_le hxx)
  have hh := hA _ hin
  rw [qFirstDensityFactor_bundle,qMetricDensityFactor_at_height hg z hp hne,
    Real.norm_eq_abs,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh
  have hnonneg := abs_nonneg (forcingCoefficient g z p)
  linarith [le_max_left A 0]

theorem exists_actual_curvatureDensity_bound (G : ℝ) (hG : 0 ≤ G) {d : ℝ} (hd : 0 < d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (g : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ∀ p ∈ U,
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      d ≤ (g p).det → |curvatureDensity g p| ≤ D := by
  obtain ⟨C,hC⟩ := (curvatureFirstTube_isCompact G d).exists_bound_of_continuousOn
    (curvatureFirstFunction_contDiffOn.continuousOn.mono (curvatureFirstTube_subset_domain G hd))
  refine ⟨2*G+max C 0,by positivity,?_⟩
  intro g U hg hU p hp hjet hdet
  have hfirst : ‖actualCurvatureFirstInput g p‖ ≤ G := by
    apply actual_first_input_norm_le hG
    · intro i j
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hjet i j 0 (by norm_num)
    · intro i j k
      exact (norm_iteratedCoordPartial_le_jet (hg.1 j k) hU [i] hp).trans
        (hjet j k 1 (by norm_num))
  have hin : actualCurvatureFirstInput g p ∈ curvatureFirstTube G d :=
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hfirst,hdet⟩
  have hlow : |curvatureLowerTerm g p| ≤ max C 0 := by
    exact (hC _ hin).trans (le_max_left _ _)
  have hsecond (i j k l : Fin 2) : |coordPartial i (coordPartial j (fun q => g q k l)) p| ≤ G :=
    (norm_iteratedCoordPartial_le_jet (hg.1 k l) hU [i,j] hp).trans (hjet k l 2 (by norm_num))
  have habs : |coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p+
      coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p| ≤ 2*G :=
    (abs_add_le _ _).trans ((add_le_add (hsecond 0 0 1 1) (hsecond 1 1 0 0)).trans_eq (by ring))
  have hhalf : |(coordPartial 0 (coordPartial 0 (fun q => g q 1 1)) p+
      coordPartial 1 (coordPartial 1 (fun q => g q 0 0)) p)/2| ≤ G := by
    rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  unfold curvatureDensity
  rw [gaussianCurvature_density_principal_part hg hU hp]
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_sub _ _).trans ((add_le_add (hsecond 0 1 0 1) hhalf).trans_eq (by ring))) hlow))

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ActualLowMetricFloor
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem exists_metric_value_det_tolerance
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) :
    ∃ d epsilon : ℝ, 0 < d ∧ 0 < epsilon ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      ∀ (g : MetricField) (p : Coord), p ∈ modelSquare →
        (∀ i j : Fin 2, |g p i j-gStar p i j| ≤ epsilon) → d ≤ (g p).det := by
  obtain ⟨B,hB,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV 0
  obtain ⟨d0,hd0,hfloor⟩ := modelSquare_isCompact.exists_forall_le'
    ((metricDet_contDiffOn hgStar).continuousOn.mono hSV)
    (fun p hp => (hgStar.2 p (hSV hp)).det_pos)
  let D := 4*B+2
  have hD : 0 < D := by dsimp [D] <;> positivity
  let epsilon := min 1 (d0/(2*D))
  have he : 0 < epsilon := by dsimp [epsilon] <;> positivity
  refine ⟨d0/2,epsilon,by positivity,he,?_,?_⟩
  · intro p hp
    exact (by linarith : d0/2 ≤ d0).trans (hfloor p hp)
  intro g p hp hclose
  have hgB : ‖gStar p‖ ≤ B := by
    apply (Matrix.norm_le_iff hB).2
    intro i j
    simpa only [norm_iteratedFDeriv_zero] using hbase i j 0 le_rfl p hp
  have hdist : ‖g p-gStar p‖ ≤ epsilon := by
    apply (Matrix.norm_le_iff he.le).2
    intro i j
    simpa only [Matrix.sub_apply,Real.norm_eq_abs] using hclose i j
  have hdetdiff := det_sub_le_small_first_distance (gStar p) (g p) hB he.le
    (min_le_left _ _) hgB hdist
  have hsmall : D*epsilon ≤ d0/2 := by
    have htwoD : (0 : ℝ) < 2*D := mul_pos (by norm_num) hD
    have h := (le_div_iff₀ htwoD).mp (min_le_right 1 (d0/(2*D)))
    change epsilon*(2*D) ≤ d0 at h
    nlinarith
  have hdif : |(g p).det-(gStar p).det| ≤ d0/2 := hdetdiff.trans hsmall
  linarith [(abs_le.mp hdif).1,hfloor p hp]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ActualTestMetricPositive
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem metricQuadraticValue_sub_bound {A B : MetricMatrix} {v : Coord} {epsilon : ℝ}
    (he : 0 ≤ epsilon) (hv : ‖v‖ ≤ 1)
    (hAB : ∀ i j, |A i j-B i j| ≤ epsilon) :
    |metricQuadraticValue A v-metricQuadraticValue B v| ≤ 4*epsilon := by
  have hvB (i : Fin 2) : |v i| ≤ 1 := (norm_le_pi_norm v i).trans hv
  have hterm (i j : Fin 2) : |v i*(A i j-B i j)*v j| ≤ epsilon := by
    rw [abs_mul,abs_mul]
    have hleft : |v i| * |A i j-B i j| ≤ epsilon :=
      (mul_le_mul (hvB i) (hAB i j) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    exact (mul_le_mul hleft (hvB j) (abs_nonneg _) he).trans_eq (mul_one _)
  have heq : metricQuadraticValue A v-metricQuadraticValue B v =
      (v 0*(A 0 0-B 0 0)*v 0+v 0*(A 0 1-B 0 1)*v 1)+
        (v 1*(A 1 0-B 1 0)*v 0+v 1*(A 1 1-B 1 1)*v 1) := by
    simp only [metricQuadraticValue,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add
    ((abs_add_le _ _).trans (add_le_add (hterm 0 0) (hterm 0 1)))
    ((abs_add_le _ _).trans (add_le_add (hterm 1 0) (hterm 1 1)))).trans_eq (by ring))

theorem exists_metric_positive_value_tolerance
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ p ∈ modelSquare, ∀ A : MetricMatrix,
      A.IsHermitian → (∀ i j, |A i j-gStar p i j| ≤ epsilon) → A.PosDef := by
  let T := modelSquare ×ˢ Metric.sphere (0 : Coord) 1
  have hT : IsCompact T := modelSquare_isCompact.prod (isCompact_sphere (0 : Coord) 1)
  have hcont : ContinuousOn (fun pv : Coord × Coord => metricQuadraticValue (gStar pv.1) pv.2) T := by
    intro pv hpv
    apply (metricQuadraticValue_continuousAt (fun i j =>
      (((hgStar.1 i j).contDiffAt (hV.mem_nhds (hSV hpv.1))).continuousAt.comp
        continuous_fst.continuousAt)) (fun i => by fun_prop)).continuousWithinAt
  have hpos (pv : Coord × Coord) (hpv : pv ∈ T) : 0 < metricQuadraticValue (gStar pv.1) pv.2 := by
    have hnorm : ‖pv.2‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hpv.2
    have hne : pv.2 ≠ 0 := by intro he; rw [he,norm_zero] at hnorm; norm_num at hnorm
    simpa only [metricQuadraticValue,star_trivial] using (hgStar.2 pv.1 (hSV hpv.1)).dotProduct_mulVec_pos hne
  obtain ⟨lambda,hlambda,hfloor⟩ := hT.exists_forall_le' hcont hpos
  refine ⟨lambda/8,by positivity,?_⟩
  intro p hp A hA hclose
  apply posDef_of_positive_on_sphere hA
  intro v hv
  have hnorm : ‖v‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hv
  have hdiff := metricQuadraticValue_sub_bound (by positivity : 0 ≤ lambda/8) hnorm.le hclose
  have hl := hfloor (p,v) ⟨hp,hv⟩
  linarith [(abs_le.mp hdiff).1]

theorem testMetric_isHermitian {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (q0 a : ℝ) (N : ℕ) (delta tau : ℝ)
    {p : Coord} (hp : p ∈ V) : (testMetric gStar q0 a N delta tau p).IsHermitian := by
  have hT : (pulseTensor q0 a N delta tau p).IsHermitian := by
    change (pulseTensor q0 a N delta tau p)ᴴ=pulseTensor q0 a N delta tau p
    ext i j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using pulseTensor_symmetric q0 a N delta tau p j i
  exact (hgStar.2 p hp).isHermitian.add hT

theorem testMetric_positive_on_modelSquare_eventually
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    (q0 a : ℝ) (ha : 0 < a) (N : ℕ) (hN : 0 < N) (delta : ℝ) :
    ∀ᶠ tau : ℕ in atTop, ∀ p ∈ modelSquare,
      (testMetric gStar q0 a N delta (tau : ℝ) p).PosDef := by
  obtain ⟨epsilon,he,hpositive⟩ := exists_metric_positive_value_tolerance hgStar hV hSV
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha 0 N hN delta he]
    with tau hpulse
  intro p hp
  apply hpositive p hp _ (testMetric_isHermitian hgStar q0 a N delta (tau : ℝ) (hSV hp))
  intro i j
  have hh := hpulse.2 i j 0 le_rfl p
  simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,testMetric,Pi.add_apply,Matrix.add_apply,
    add_sub_cancel_left] using hh

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualQPointBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
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

theorem exists_actual_Q_point_bounds_from_reference_floor
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G d c kappa q0 r : ℝ} (M : ℕ) (hG : 0 ≤ G) (hd : 0 < d) (hc : 0 < c)
    (hgStarB : ∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G)
    (hdStar : ∀ p ∈ modelSquare, d ≤ (gStar p).det)
    (hq0 : |q0| ≤ 1/20) (hr : 0 < r) (hLr : boundedClassWidth kappa M*r ≤ 1/20)
    (N : ℕ) (hN : 1 < N) :
    ∃ A D dcompare : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ 0 < dcompare ∧
      ∀ delta : ℝ, 0 < delta → ∀ᶠ tau : ℕ in atTop,
        2 ≤ tau ∧ N ≤ tau ∧
        SmoothPositiveOn (testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ)) modelOpenSquare ∧
        ∀ (gTau : MetricField) (U : Set Coord) (z : Coord → ℝ),
          SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
          BoundedAdmissibleHeight gTau M z →
          (∀ i j k, k ≤ 2 → ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
          (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
          (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
            ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
              testMetric gStar q0 (boundedClassWidth kappa M*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                metricApproximationAccuracy tau) →
          (∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            c ≤ |covHessian (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0) p 0 0|) →
          ∀ p ∈ pulseStrip (boundedClassWidth kappa M*r/2) delta (tau : ℝ),
            QPulsePointBounds gStar gTau z modelOpenSquare q0 (boundedClassWidth kappa M*r/16)
              delta (tau : ℝ) N (8*G) (G+1) (max (8*G) (boundedClassShearedStateBudget q0 M))
              D A d dcompare c (metricApproximationAccuracy tau)
              (qPulseFirstJetBudget (boundedClassWidth kappa M*r/16)
                (div_pos (mul_pos (boundedClassWidth_pos kappa M) hr) (by norm_num)) N delta (tau : ℝ)) p := by
  let L := boundedClassWidth kappa M
  let a := L*r/16
  let BQ := max (8*G) (boundedClassShearedStateBudget q0 M)
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have ha : 0 < a := div_pos (mul_pos hL hr) (by norm_num)
  have hq1 : |q0| ≤ 1 := hq0.trans (by norm_num)
  obtain ⟨A,hA,hforce⟩ := exists_actual_forcingCoefficient_bound BQ hd hc
  obtain ⟨D,hD,hdensity⟩ := exists_actual_curvatureDensity_bound G hG hd
  obtain ⟨dcompare,epsilon,hdcompare,he,_,hdetTolerance⟩ := exists_metric_value_det_tolerance hgStar hV hSV
  have hOV : modelOpenSquare ⊆ V := modelOpenSquare_subset.trans hSV
  have hgStarO : SmoothPositiveOn gStar modelOpenSquare :=
    ⟨fun i j => (hgStar.1 i j).mono hOV,fun p hp => hgStar.2 p (hOV hp)⟩
  refine ⟨A,D,dcompare,hA,hD,hdcompare,?_⟩
  intro delta hdelt
  have hwidth : ∀ᶠ tau : ℕ in atTop, 1 ≤ (tau : ℝ) ∧ delta/(2*(tau : ℝ)) ≤ r/4 :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun tau : ℕ => (tau : ℝ)) atTop atTop).eventually
      (pulse_width_eventually hr delta)
  filter_upwards [testMetric_positive_on_modelSquare_eventually hgStar hV hSV q0 a ha N (by omega) delta,
    pulseTensor_finite_coeff_jets_eventually_small q0 a ha 1 N hN delta (by norm_num : (0 : ℝ) < 1),
    pulseTensor_finite_coeff_jets_eventually_small q0 a ha 0 N (by omega) delta he,
    hwidth,eventually_ge_atTop 2,eventually_ge_atTop N] with tau hpositive hsmall hsmall0 hw ht2 htN
  let test := testMetric gStar q0 a N delta (tau : ℝ)
  have htest : SmoothPositiveOn test modelOpenSquare :=
    ⟨fun i j => (testMetric_coeff_contDiffOn hgStar q0 a N delta (tau : ℝ) i j).mono hOV,
      fun p hp => hpositive p (modelOpenSquare_subset hp)⟩
  refine ⟨ht2,htN,htest,?_⟩
  intro gTau U z hgTau hU hSU hclass hgB hdet happ href p hp
  have hbr : delta/(tau : ℝ) ≤ r := by
    have heq : delta/(tau : ℝ)=2*(delta/(2*(tau : ℝ))) := by ring
    rw [heq]
    linarith [hw.2]
  have hx : |p 0| ≤ L*r := (abs_le.mpr hp.1).trans (by linarith [mul_pos hL hr])
  have ht : |p 1| ≤ r := (abs_le.mpr hp.2).trans hbr
  have hL1 : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M)
  have hpC := inverseShear_slab_mem_centralBox hL1 hr.le hLr hq0 hx ht
  have hpO := centralBox_subset_modelOpenSquare hpC
  have hpS := centralBox_subset_modelSquare hpC
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgTauO : SmoothPositiveOn gTau modelOpenSquare :=
    ⟨fun i j => (hgTau.1 i j).mono hOU,fun p hp => hgTau.2 p (hOU hp)⟩
  have hfirst := sheared_first_input_norm_le_of_original_jets hgStar hV (hSV hpS) hG hq1
    (fun i j k hk => hgStarB i j k (by omega) _ hpS)
  have hdetRef : d ≤ (metricInShearCoordinates gStar q0 p).det := by
    rw [metricDet_in_shear_coordinates]
    exact hdStar _ hpS
  have htestJet (i j : Fin 2) (k : ℕ) (hk : k ≤ 1) :
      ‖iteratedFDeriv ℝ k (fun q => test q i j) (inverseShearCoordinates q0 p)‖ ≤ G+1 := by
    have hps : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta (tau : ℝ) q i j) :=
      (contDiff_apply ℝ ℝ j).comp
        ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta (tau : ℝ)))
    change ‖iteratedFDeriv ℝ k ((fun q => gStar q i j)+
      (fun q => pulseTensor q0 a N delta (tau : ℝ) q i j)) (inverseShearCoordinates q0 p)‖ ≤ _
    rw [iteratedFDeriv_add_apply
      (((hgStar.1 i j).contDiffAt (hV.mem_nhds (hSV hpS))).of_le (WithTop.coe_le_coe.mpr le_top))
      (hps.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))]
    exact (norm_add_le _ _).trans (add_le_add (hgStarB i j k (by omega) _ hpS) (hsmall.2 i j k hk _))
  have htestFirst : ‖actualCurvatureFirstInput test (inverseShearCoordinates q0 p)‖ ≤ G+1 := by
    apply actual_first_input_norm_le (by linarith)
    · intro i j
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using htestJet i j 0 (by norm_num)
    · intro i j k
      exact (norm_iteratedCoordPartial_le_jet (htest.1 j k) modelOpenSquare_isOpen [i] hpO).trans
        (htestJet j k 1 le_rfl)
  have htestDet : dcompare ≤ (test (inverseShearCoordinates q0 p)).det := by
    apply hdetTolerance _ _ hpS
    intro i j
    have hh := hsmall0.2 i j 0 le_rfl (inverseShearCoordinates q0 p)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,test,testMetric,Pi.add_apply,
      Matrix.add_apply,add_sub_cancel_left] using hh
  have herr := actual_metric_jet_approximation_inputs hgTauO htest modelOpenSquare_isOpen hpO
    (fun i j k hk => happ i j k (hk.trans ht2) _ hpS)
  have hstate : ‖qSolutionJet (heightInShearCoordinates z q0) p‖ ≤ boundedClassShearedStateBudget q0 M := by
    apply bounded_class_sheared_solution_state_bound hclass q0 hpS
    refine ⟨hx.trans (hLr.trans (by norm_num)),ht.trans ?_⟩
    have hrsmall : r ≤ L*r := by nlinarith
    exact hrsmall.trans (hLr.trans (by norm_num))
  have hbundle : ‖qFirstBundle (metricInShearCoordinates gStar q0)
      (qSolutionJet (heightInShearCoordinates z q0) p)‖ ≤ BQ := by
    change max ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0)
      (statePoint (qSolutionJet (heightInShearCoordinates z q0) p))‖
      ‖qSolutionJet (heightInShearCoordinates z q0) p‖ ≤ BQ
    rw [statePoint_qSolutionJet]
    exact max_le_max hfirst hstate
  have hbase := actual_sheared_first_jet_error_from_Ctau hgStarO htest hgTauO modelOpenSquare_isOpen
    hq1 ha (by omega : 0 < N) ht2 (by omega : N-1 ≤ tau) hpO
      (fun i j k hk => happ i j k hk _ hpS)
  have hdetTau : d ≤ (gTau (inverseShearCoordinates q0 p)).det := by
    have hh := hdet _ hpS
    rwa [abs_of_pos (hgTau.2 _ (hSU hpS)).det_pos] at hh
  have hDactual := hdensity gTau U hgTau hU _ (hSU hpS)
    (fun i j k hk => hgB i j k hk _ hpS) hdetTau
  have hAactual := hforce (metricInShearCoordinates gStar q0) (heightInShearCoordinates z q0)
    (inverseShearCoordinates q0 ⁻¹' V) (metricInShearCoordinates_smoothPositive hgStar q0)
      p (hSV hpS) hbundle hdetRef (href p hp)
  exact ⟨hpO,hfirst,hdetRef,htestFirst,htestDet,herr.1,herr.2,hbundle,href p hp,hbase,hDactual,hAactual⟩

end SmoothLocal.Perturbation

end

end OAI
end


