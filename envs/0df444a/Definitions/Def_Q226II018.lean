-- Prove2me | Definitions.Def_Q226II018
-- name    : Q226II018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:58:49.774199+00:00
-- url     : https://prove2.me/theorems/7159e06e-2e0c-4342-93e7-9346e73df12e
-- title:
--   Definitions bundle Q226II018 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 12 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`IsometricImmersion_Caps_ActualFiniteLowerCutBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Caps/ActualFiniteLowerCutBounds.lean), [`IsometricImmersion_Caps_ReflectedActualCapFlow`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Caps/ReflectedActualCapFlow.lean), [`IsometricImmersion_Comparison_ActualComparisonEnergy`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Comparison/ActualComparisonEnergy.lean), [`IsometricImmersion_Comparison_ActualComparisonGradient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Comparison/ActualComparisonGradient.lean), [`IsometricImmersion_Comparison_CurvatureComparisonControl`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Comparison/CurvatureComparisonControl.lean), [`IsometricImmersion_Coordinates_ActualFiniteShearedCutBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Coordinates/ActualFiniteShearedCutBounds.lean), [`IsometricImmersion_Estimates_ActualQMomentLower`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Estimates/ActualQMomentLower.lean), [`IsometricImmersion_Metrics_ActualLowMetricFloor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Metrics/ActualLowMetricFloor.lean), [`IsometricImmersion_Pulses_PulseDensityGlobal`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Pulses/PulseDensityGlobal.lean), [`IsometricImmersion_Taylor_TaylorRemainderBound`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Taylor/TaylorRemainderBound.lean).
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II014`, `Q226II015` and `Q226II016` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q226II019`.
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
import Mathlib.Analysis.Calculus.ContDiff.Basic
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
import Mathlib.Analysis.Calculus.Taylor
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
import Mathlib.Data.Nat.Choose.Sum
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
import Definitions.Def_Q226II014
import Definitions.Def_Q226II015
import Definitions.Def_Q226II016

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_ActualFiniteLowerCutBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Analytic

theorem exists_actual_finite_lower_cut_height_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
          ∀ᶠ tau : ℕ in atTop,
            ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
              SmoothPositiveOn gTau U → IsOpen U →
              (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
              (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
              CapInductionHeight gTau U Z c e0 z →
              CapInductionFlow gTau U G Z d c e0 kappa z Y W →
              |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
              (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                  testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                    metricApproximationAccuracy tau) →
              ∀ ds : List (Fin 2), ds.length ≤ n → ∀ t : ℝ, |t| ≤ L*r →
                |iteratedCoordPartial ds z (inverseShearCoordinates q0 (boxPoint t (-r)))| ≤ C := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hmetric⟩ :=
    exists_actual_finite_cap_metric_budgets (e0 := e0) (kappa := kappa)
      hgStar hV hSV hG hZ hd hc hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro n
  obtain ⟨Bmetric,hBmetric,hlocal⟩ := hmetric n 0
  let R := lowerCutRectangle L r hL hr hrhalf hLr
  let J : CapMetricJetBudget (-r/2) := fun _ _ => Bmetric
  obtain ⟨C,hC,hheight⟩ := uniform_finite_varying_lowerCap_pointwise
    G Z d c e0 kappa hG hZ hd hc J n R (fun _ _ => hBmetric)
  refine ⟨C,hC,?_⟩
  intro N delta hdelta
  filter_upwards [hlocal N delta hdelta] with tau htau
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox ds hds t ht
  have hrequests : FiniteCapMetricJets gTau Y J (lowerCapPointwiseRequests n R) :=
    (htau.2 gTau U W z Y hgTau hU hh hf hcenter happrox).1 R
  have hbound := hheight gTau U z Y W hgTau hU (hf.squareSubset.trans hf.domainSubset)
    hg4 hdet hh hf hrequests
  have hp : inverseShearCoordinates q0 (boxPoint t (-r)) ∈ R.image Y :=
    actual_lower_cut_in_cap_image hh hf hG hZ hd hc hL hr hrhalf hLr hq0 hcenter hrsmall ht
  exact hbound ds hds _ hp

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_ReflectedActualCapFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Flow.Reflection SmoothLocal.Model

theorem exists_actual_reflected_capInductionFlow
    {g0 : MetricField} {kappa G Z d c e0 : ℝ} (eta : metricPatchSet g0 kappa)
    {U : Set Coord} {z : Coord → ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hg : SmoothPositiveOn (perturbedMetric g0 eta.val) U)
    (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => perturbedMetric g0 eta.val q i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hh : CapInductionHeight (perturbedMetric g0 eta.val) U Z c e0 z)
    (hk : 0 < kappa) (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∃ (W : Set Coord) (Y : ℝ → ℝ → ℝ),
      CapInductionFlow (reflectedMetric (perturbedMetric g0 eta.val)) (reflectPoint ⁻¹' U)
        G Z d c e0 kappa (reflectedScalar z) Y W := by
  have hsum : reflectedMetric g0+reflectedMetric (perturbationTensor eta.val) =
      reflectedMetric (perturbedMetric g0 eta.val) :=
    (reflectedMetric_add g0 (perturbationTensor eta.val)).symm
  have hgR : SmoothPositiveOn
      (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) (reflectPoint ⁻¹' U) := by
    rw [hsum]
    exact reflectedMetric_smoothPositive hg
  have hhR : CapInductionHeight
      (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val))
      (reflectPoint ⁻¹' U) Z c e0 (reflectedScalar z) := by
    rw [hsum]
    exact reflected_capInductionHeight hg hU hSU hh
  have hBR : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q =>
        (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) q i j) p‖ ≤ G := by
    rw [hsum]
    exact reflectedMetric_C8 hgB
  have hdetR : ∀ p ∈ modelSquare,
      d ≤ |((reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) p).det| := by
    intro p hp
    rw [hsum,reflectedMetric_det]
    exact hdet _ ((reflectPoint_mem_modelSquare p).mpr hp)
  have hcentralR : ∀ p ∈ centralBox,
      gaussianCurvature (reflectedMetric g0+reflectedMetric (perturbationTensor eta.val)) p < -kappa/2 := by
    intro p hp
    have hpr : reflectPoint p ∈ centralBox :=
      (reflectPoint_mem_symmetricSquare (1/5) p).mpr hp
    rw [hsum,reflectedMetric_curvature hg hU (hSU (centralBox_subset_modelSquare hpr))]
    exact eta.property.2 _ hpr
  obtain ⟨W,Y,hflow⟩ := exists_capInductionFlow hgR (reflectedDomain_isOpen hU)
    (reflectedDomain_contains_modelSquare hSU) hG hZ hd hc he0 hBR hdetR hhR hk
    (reflectedMetric_model hg0 hU hbackground)
    (reflectedMetric_support_patch (perturbationTensor_tsupport_subset eta.val)) hcentralR
  exact ⟨W,Y,by simpa only [hsum] using hflow⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_CurvatureComparisonControl
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

theorem exists_uniform_curvature_density_comparison (B : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g h : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn h U → IsOpen U →
      ∀ p ∈ U, ∀ e : ℝ,
        ‖actualCurvatureFirstInput h p‖ ≤ B → d ≤ (h p).det →
        ‖actualCurvatureFirstInput g p-actualCurvatureFirstInput h p‖ ≤ e →
        e ≤ 1 → (4*max B 0+2)*e ≤ d/2 →
        (∀ i j k l : Fin 2,
          |coordPartial i (coordPartial j (fun q => g q k l)) p-
            coordPartial i (coordPartial j (fun q => h q k l)) p| ≤ e) →
        |curvatureDensity g p-curvatureDensity h p| ≤ C*e := by
  obtain ⟨C0,hC0,hbound⟩ := exists_uniform_curvature_first_comparison B hd
  refine ⟨2+C0,by linarith,?_⟩
  intro g h U hg hh hU p hp e hjet hdet hdist he1 hsmall hsecond
  have hscale : 0 ≤ 4*max B 0+2 := by linarith [le_max_right B 0]
  have hfirst := hbound (actualCurvatureFirstInput h p) (actualCurvatureFirstInput g p)
    hjet hdet (hdist.trans he1) ((mul_le_mul_of_nonneg_left hdist hscale).trans hsmall)
  have hL : |curvatureLowerTerm g p-curvatureLowerTerm h p| ≤ C0*e :=
    hfirst.trans (mul_le_mul_of_nonneg_left hdist hC0)
  rw [←curvatureDensityJetError_eq hg hh hU hp]
  exact ((curvatureDensityJetError_le g h p (hsecond 0 1 0 1) (hsecond 0 0 1 1)
    (hsecond 1 1 0 0)).trans (add_le_add le_rfl hL)).trans_eq (by ring)

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

theorem exists_actual_density_global_bound (B Bcompare : ℝ) {d dcompare : ℝ}
    (hd : 0 < d) (hdcompare : 0 < dcompare)
    {a : ℝ} (ha : 0 < a) (N : ℕ) (hN : 1 < N) :
    ∃ Ctest Ccompare : ℝ, 0 ≤ Ctest ∧ 0 ≤ Ccompare ∧
      ∀ delta : ℝ, 0 < delta → ∃ T : ℝ, 1 ≤ T ∧
        ∀ tau : ℝ, T ≤ tau → ∀ (gStar gTau : MetricField) (q0 : ℝ) (U : Set Coord),
          SmoothPositiveOn gStar U →
          SmoothPositiveOn (testMetric gStar q0 a N delta tau) U →
          SmoothPositiveOn gTau U → IsOpen U →
          ∀ p : Coord, inverseShearCoordinates q0 p ∈ U →
            ‖actualCurvatureFirstInput (metricInShearCoordinates gStar q0) p‖ ≤ B →
            d ≤ (metricInShearCoordinates gStar q0 p).det →
            ∀ epsilon : ℝ,
              ‖actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
                (inverseShearCoordinates q0 p)‖ ≤ Bcompare →
              dcompare ≤ (testMetric gStar q0 a N delta tau
                (inverseShearCoordinates q0 p)).det →
              ‖actualCurvatureFirstInput gTau (inverseShearCoordinates q0 p)-
                actualCurvatureFirstInput (testMetric gStar q0 a N delta tau)
                  (inverseShearCoordinates q0 p)‖ ≤ epsilon →
              epsilon ≤ 1 → (4*max Bcompare 0+2)*epsilon ≤ dcompare/2 →
              (∀ i j k l : Fin 2,
                |coordPartial i (coordPartial j (fun q => gTau q k l))
                    (inverseShearCoordinates q0 p)-
                  coordPartial i (coordPartial j
                    (fun q => testMetric gStar q0 a N delta tau q k l))
                    (inverseShearCoordinates q0 p)| ≤ epsilon) →
              |(curvatureDensity gTau (inverseShearCoordinates q0 p)-
                  curvatureDensity gStar (inverseShearCoordinates q0 p))-
                pulsePrincipalLeading a N delta tau p| ≤
                testDensityErrorCoefficient Ctest a ha delta*tau/tau^N+
                  Ccompare*epsilon := by
  obtain ⟨Ct,hCt,htest⟩ := exists_test_density_global_bound B hd ha N hN
  obtain ⟨Cc,hCc,hcompare⟩ := exists_uniform_curvature_density_comparison Bcompare hdcompare
  refine ⟨Ct,Cc,hCt,hCc,?_⟩
  intro delta hdelta
  obtain ⟨T,hT,hglobal⟩ := htest delta hdelta
  refine ⟨T,hT,?_⟩
  intro tau ht gStar gTau q0 U hgStar hgTest hgTau hU p hpU hjet hdet
    epsilon hjetTest hdetTest hdistance he1 hesmall hsecond
  have hpulse := hglobal tau ht gStar q0 U hgStar hgTest hU p hpU hjet hdet
  have hmetric := hcompare gTau (testMetric gStar q0 a N delta tau) U
    hgTau hgTest hU (inverseShearCoordinates q0 p) hpU epsilon
    hjetTest hdetTest hdistance he1 hesmall hsecond
  have heq :
      (curvatureDensity gTau (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-
          pulsePrincipalLeading a N delta tau p =
      ((curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)-
        curvatureDensity gStar (inverseShearCoordinates q0 p))-
          pulsePrincipalLeading a N delta tau p)+
      (curvatureDensity gTau (inverseShearCoordinates q0 p)-
        curvatureDensity (testMetric gStar q0 a N delta tau) (inverseShearCoordinates q0 p)) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hpulse hmetric)

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

theorem sheared_Q_on_height_contDiffOn {g : MetricField} {z : Coord → ℝ}
    {U S : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) (hSU : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ U)
    (hxx : ∀ p ∈ S, covHessian (metricInShearCoordinates g q0)
      (heightInShearCoordinates z q0) p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => sixVariableQ (metricInShearCoordinates g q0)
      (qSolutionJet (heightInShearCoordinates z q0) p)) S := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  have hV : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgV : SmoothPositiveOn (metricInShearCoordinates g q0) V := by
    simpa only [V,metricInShearCoordinates,inverseShearCoordinates_eq_affine] using
      affinePullbackMetric_smoothPositive hg 0 (inverseShearMatrix q0)
        (Matrix.mulVec_injective_of_isUnit (inverseShearMatrix_isUnit q0))
  have hzV : ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) V :=
    heightInShearCoordinates_contDiffOn hz q0
  have hSV : S ⊆ V := fun p hp => hSU p hp
  apply (sixVariableQ_contDiffOn hgV hV).comp ((qSolutionJet_contDiffOn hV hzV).mono hSV)
  intro p hp
  change statePoint (qSolutionJet (heightInShearCoordinates z q0) p) ∈ V ∧
    stateQDenominator (metricInShearCoordinates g q0)
      (qSolutionJet (heightInShearCoordinates z q0) p) ≠ 0
  rw [statePoint_qSolutionJet,stateQDenominator_qSolutionJet]
  exact ⟨hSV hp,hxx p hp⟩

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonEnergy
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem metricComparisonSource_contDiffOn
    {g gRef : MetricField} {P z : Coord → ℝ} {V : Set Coord}
    (hg : SmoothPositiveOn g V) (hgRef : SmoothPositiveOn gRef V) (hV : IsOpen V)
    (hP : ContDiffOn ℝ ∞ P V) (hz : ContDiffOn ℝ ∞ z V)
    (hxx : ∀ p ∈ V, covHessian g z p 0 0 ≠ 0)
    (hrefz : ∀ p ∈ V, covHessian gRef z p 0 0 ≠ 0)
    (hrefP : ∀ p ∈ V, covHessian gRef P p 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (metricComparisonSource g gRef P z) V := by
  have hzJet := qSolutionJet_contDiffOn hV hz
  have hPJet := qSolutionJet_contDiffOn hV hP
  have hQ := (sixVariableQ_contDiffOn hg hV).comp hzJet
    (fun p hp => qSolutionJet_mem_domain hp (hxx p hp))
  have hQz := (sixVariableQ_contDiffOn hgRef hV).comp hzJet
    (fun p hp => qSolutionJet_mem_domain hp (hrefz p hp))
  have hQP := (sixVariableQ_contDiffOn hgRef hV).comp hPJet
    (fun p hp => qSolutionJet_mem_domain hp (hrefP p hp))
  exact (hQ.sub hQz).sub ((partial_contDiffOn (partial_contDiffOn hP hV 1) hV 1).sub hQP)

theorem exists_actual_comparison_energy
    {gRef : MetricField} {U S : Set Coord}
    (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c s0 : ℝ} (hc : 0 < c) (hs0 : 0 < s0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : MetricField) (P z : Coord → ℝ) (V : Set Coord)
      (boxRadius width a b : ℝ),
      IsOpen V → V ⊆ U → SmoothPositiveOn g V →
      ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V →
      0 < width → width < boxRadius → a ≤ b →
      closedRectangle (-boxRadius) boxRadius a b ⊆ V →
      closedRectangle (-boxRadius) boxRadius a b ⊆ S →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ‖p‖ ≤ R) →
      CoordinateBound P (closedRectangle (-boxRadius) boxRadius a b) 3 Z0 →
      CoordinateBound z (closedRectangle (-boxRadius) boxRadius a b) 3 Z →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b,
        (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator gRef (qHeightJetSegment P z sigma p)| ∧
          s0 ≤ qFirstCoefficient gRef 5 (qHeightJetSegment P z sigma p)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius, P (boxPoint x a)=z (boxPoint x a)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius,
        coordPartial 1 P (boxPoint x a)=coordPartial 1 z (boxPoint x a)) →
      2*comparisonEnergySpeed C*(b-a)<2*width →
      Real.sqrt (movingEnergy (-width) width a (comparisonEnergySpeed C)
        (comparisonCoefficient gRef P z 5) (comparisonDifference P z) b) ≤
        Real.exp (comparisonEnergyRate C Z0 Z s0*(b-a))*
          ∫ t in a..b, movingSourceNorm (-width) width a (comparisonEnergySpeed C)
            (metricComparisonSource g gRef P z) t := by
  obtain ⟨C,hC,hbounds⟩ := exists_uniform_comparison_coefficient_bounds hgRef hU hS hSU R Z0 Z hR hc
  refine ⟨C,hC,?_⟩
  intro g P z V boxRadius width a b hV hVU hg hP hz hw hwR hab hboxV hboxS hpB hPZ hzZ
    hD hxx hmargin hvalue hvelocity hlength
  let T := closedRectangle (-boxRadius) boxRadius a b
  let speed := comparisonEnergySpeed C
  let MC := C*(max 1 Z0+max 1 Z)
  have hgRefV : SmoothPositiveOn gRef V := hgRef.mono hVU
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hs : 0 ≤ speed := add_nonneg hCp.le (Real.sqrt_nonneg _)
  have hMC : 0 ≤ MC := mul_nonneg hCp.le (by positivity)
  have hCmc : C ≤ MC := by
    have hsum : 1 ≤ max 1 Z0+max 1 Z := by
      linarith [le_max_left (1 : ℝ) Z0,le_max_left (1 : ℝ) Z]
    exact le_mul_of_one_le_right hCp.le hsum
  have hseg : ∀ p ∈ T, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef V := by
    intro p hp sigma hsigma
    refine ⟨by simpa only [statePoint_qHeightJetSegment] using hboxV hp,?_⟩
    exact abs_pos.mp (hc.trans_le (hmargin p hp sigma hsigma).1)
  obtain ⟨W,hW,hTW,hWV,hWseg,hcoeffSmooth⟩ := exists_comparison_coefficient_neighborhood
    hgRefV hV hP hz (closedRectangle_compact _ _ _ _) hboxV hseg
  let V0 := W ∩ (fun p => covHessian g z p 0 0) ⁻¹' ({0}ᶜ : Set ℝ)
  have hV0 : IsOpen V0 := ((covHessian_contDiffOn hg hV hz 0 0).continuousOn.mono hWV).isOpen_inter_preimage
    hW isClosed_singleton.isOpen_compl
  have hTV0 : T ⊆ V0 := fun p hp => ⟨hTW hp,hxx p hp⟩
  obtain ⟨radius,lo,hi,hRad,hlo,hhi,hrect⟩ := exists_containing_coordinateRectangle hV0
    (hw.trans hwR) hab hTV0
  let Rect := coordinateRectangle radius lo hi
  have hRect : IsOpen Rect := coordinateRectangle_isOpen _ _ _
  have hRectW : Rect ⊆ W := fun p hp => (hrect hp).1
  have hRectV : Rect ⊆ V := hRectW.trans hWV
  have hgsR : SmoothPositiveOn gRef Rect := hgRefV.mono hRectV
  have hgR : SmoothPositiveOn g Rect := hg.mono hRectV
  have hPR := hP.mono hRectV
  have hzR := hz.mono hRectV
  have hxR : ∀ p ∈ Rect, covHessian g z p 0 0 ≠ 0 := fun p hp => (hrect hp).2
  have hsegR : ∀ p ∈ Rect, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef Rect := by
    intro p hp sigma hsigma
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hp,(hWseg p (hRectW hp) sigma hsigma).2⟩
  have hrefP : ∀ p ∈ Rect, covHessian gRef P p 0 0 ≠ 0 := by
    intro p hp
    simpa only [qHeightJetSegment,stateSegment_zero,stateQDenominator_qSolutionJet] using
      (hsegR p hp 0 (by norm_num)).2
  have hrefz : ∀ p ∈ Rect, covHessian gRef z p 0 0 ≠ 0 := by
    intro p hp
    simpa only [qHeightJetSegment,stateSegment_one,stateQDenominator_qSolutionJet] using
      (hsegR p hp 1 (by norm_num)).2
  have hsource := metricComparisonSource_contDiffOn hgR hgsR hRect hPR hzR hxR hrefz hrefP
  have hcoeffR (i : Fin 6) : ContDiffOn ℝ ∞ (comparisonCoefficient gRef P z i) Rect :=
    (hcoeffSmooth i).mono hRectW
  have hnum := hbounds P z V T hV hVU hP hz hboxS hboxV hpB hPZ hzZ
    (fun p hp sigma hsigma => (hmargin p hp sigma hsigma).1)
  have hslabT : shrinkingSlab (-width) width a b speed ⊆ T := by
    intro p hp
    change p 1 ∈ Icc a b ∧ p 0 ∈ Icc (-width+speed*(p 1-a)) (width-speed*(p 1-a)) at hp
    have hinc : 0 ≤ speed*(p 1-a) := mul_nonneg hs (sub_nonneg.mpr hp.1.1)
    exact ⟨⟨by linarith [hp.2.1],
      by linarith [hp.2.2]⟩,hp.1⟩
  have hfloor (p : Coord) (hp : p ∈ shrinkingSlab (-width) width a b speed) :
      s0 ≤ comparisonCoefficient gRef P z 5 p :=
    averagedQCoefficient_lower hgRefV hV (hseg p (hslabT hp)) 5
      (fun sigma hsigma => (hmargin p (hslabT hp) sigma hsigma).2)
  have hchar (p : Coord) (hp : p ∈ shrinkingSlab (-width) width a b speed) :
      |comparisonCoefficient gRef P z 4 p|+Real.sqrt (comparisonCoefficient gRef P z 5 p) ≤ speed :=
    add_le_add (hnum 4 p (hslabT hp)).1
      (Real.sqrt_le_sqrt ((le_abs_self _).trans (hnum 5 p (hslabT hp)).1))
  have hEq (p : Coord) (hp : p ∈ shrinkingSlab (-width) width a b speed) :=
    comparison_equation_from_darboux hg hgRefV hV hz hP (hboxV (hslabT hp))
      (hD p (hslabT hp)) (hxx p (hslabT hp)) (hseg p (hslabT hp))
  have hprop := moving_slab_energy_propagation (hcoeffR 4) (hcoeffR 5) (hcoeffR 3) (hcoeffR 2)
    (hzR.sub hPR) hsource (hw.trans (hwR.trans hRad)) hab hs
    (by linarith) (by linarith) ⟨hlo,hab.trans_lt hhi⟩ ⟨hlo.trans_le hab,hhi⟩
    (by simpa only [sub_neg_eq_add,two_mul] using hlength) hs0 hMC hfloor
    (fun p hp => ⟨(hnum 3 p (hslabT hp)).1.trans hCmc,
      (hnum 2 p (hslabT hp)).1.trans hCmc,(hnum 4 p (hslabT hp)).2 0,
      (hnum 5 p (hslabT hp)).2 0,(hnum 5 p (hslabT hp)).2 1⟩) hchar hEq
  have hzero := comparison_initial_energy_zero (S := comparisonCoefficient gRef P z 5) hV hz hP
    (show -width ≤ width by linarith)
    (fun x hx => hboxV (by
      simpa [closedRectangle,boxPoint]
        using And.intro (And.intro hx.1.le hx.2.le) (And.intro (le_refl a) hab))) hvalue hvelocity
    (by linarith) hwR
  have hdiff : (fun x => z x-P x) = SmoothLocal.HighEquation.comparisonDifference P z := rfl
  rw [hdiff,hzero] at hprop
  simpa only [hzero,Real.sqrt_zero,zero_add,comparisonEnergyRate,MC] using hprop

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonGradient
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem exists_actual_comparison_gradient
    {gRef : MetricField} {U S : Set Coord}
    (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c s0 : ℝ} (hc : 0 < c) (hs0 : 0 < s0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (g : MetricField) (P z : Coord → ℝ) (V : Set Coord)
      (boxRadius width pulseRadius a b F : ℝ),
      IsOpen V → V ⊆ U → SmoothPositiveOn g V →
      ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V →
      0 < width → width < boxRadius → a ≤ b →
      closedRectangle (-boxRadius) boxRadius a b ⊆ V →
      closedRectangle (-boxRadius) boxRadius a b ⊆ S →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ‖p‖ ≤ R) →
      CoordinateBound P (closedRectangle (-boxRadius) boxRadius a b) 3 Z0 →
      CoordinateBound z (closedRectangle (-boxRadius) boxRadius a b) 3 Z →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b,
        (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, covHessian g z p 0 0 ≠ 0) →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator gRef (qHeightJetSegment P z sigma p)| ∧
          s0 ≤ qFirstCoefficient gRef 5 (qHeightJetSegment P z sigma p)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius, P (boxPoint x a)=z (boxPoint x a)) →
      (∀ x ∈ Ioo (-boxRadius) boxRadius,
        coordPartial 1 P (boxPoint x a)=coordPartial 1 z (boxPoint x a)) →
      0 < pulseRadius → 0 ≤ F →
      comparisonEnergySpeed C*(b-a) ≤ width-pulseRadius →
      (∀ p ∈ closedRectangle (-boxRadius) boxRadius a b, |metricComparisonSource g gRef P z p| ≤ F) →
      ∀ t ∈ Icc a b, ∀ i : Fin 2,
        Real.sqrt (∫ x in Icc (-pulseRadius) pulseRadius,
          (coordPartial i (comparisonDifference P z) (boxPoint x t))^2) ≤
          Real.sqrt (2*(1+1/s0))*
            (Real.exp (comparisonEnergyRate C Z0 Z s0*(b-a))*F*Real.sqrt (2*width)*(b-a)) := by
  obtain ⟨C,hC,henergy⟩ := exists_actual_comparison_energy hgRef hU hS hSU R Z0 Z hR hc hs0
  refine ⟨C,hC,?_⟩
  intro g P z V boxRadius width pulseRadius a b F hV hVU hg hP hz hw hwR hab
    hboxV hboxS hpB hPZ hzZ hD hxx hmargin hvalue hvelocity hpulse hF hwidth hsource
  let T := closedRectangle (-boxRadius) boxRadius a b
  let speed := comparisonEnergySpeed C
  let rate := comparisonEnergyRate C Z0 Z s0
  have hs : 0 ≤ speed := add_nonneg (zero_le_one.trans hC) (Real.sqrt_nonneg _)
  have hr : 0 ≤ rate := by unfold rate comparisonEnergyRate; positivity
  have hlength : 2*speed*(b-a)<2*width := by linarith
  have hgRefV := hgRef.mono hVU
  have hseg : ∀ p ∈ T, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef V := by
    intro p hp sigma hsigma
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hboxV hp,
      abs_pos.mp (hc.trans_le (hmargin p hp sigma hsigma).1)⟩
  obtain ⟨W,hW,hTW,hWV,_,hWsmooth⟩ := exists_comparison_coefficient_neighborhood
    hgRefV hV hP hz (closedRectangle_compact _ _ _ _) hboxV hseg
  have hSlabT {t : ℝ} (ht : t ∈ Icc a b) : shrinkingSlab (-width) width a t speed ⊆ T := by
    intro p hp
    change p 1 ∈ Icc a t ∧ p 0 ∈ Icc (-width+speed*(p 1-a)) (width-speed*(p 1-a)) at hp
    have hinc : 0 ≤ speed*(p 1-a) := mul_nonneg hs (sub_nonneg.mpr hp.1.1)
    exact ⟨⟨by linarith [hp.2.1],
      by linarith [hp.2.2]⟩,⟨hp.1.1,hp.1.2.trans ht.2⟩⟩
  intro t ht i
  have hTT : closedRectangle (-boxRadius) boxRadius a t ⊆ T :=
    fun p hp => ⟨hp.1,⟨hp.2.1,hp.2.2.trans ht.2⟩⟩
  have hlengtht : 2*speed*(t-a)<2*width := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs)
    exact hm.trans_lt hlength
  have hEt := henergy g P z V boxRadius width a t hV hVU hg hP hz hw hwR ht.1
    (hTT.trans hboxV) (hTT.trans hboxS) (fun p hp => hpB p (hTT hp))
    (fun ds hds p hp => hPZ ds hds p (hTT hp)) (fun ds hds p hp => hzZ ds hds p (hTT hp))
    (fun p hp => hD p (hTT hp)) (fun p hp => hxx p (hTT hp))
    (fun p hp sigma hsigma => hmargin p (hTT hp) sigma hsigma) hvalue hvelocity hlengtht
  have horder (s : ℝ) (hsat : s ∈ Icc a t) :
      inwardLeft (-width) a speed s ≤ inwardRight width a speed s := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hsat.2 a) hs
    dsimp [inwardLeft,inwardRight]
    linarith
  have hI := integrated_movingSourceNorm_le_of_pointwise_bound ht.1 hs hF horder
    (fun p hp => hsource p (hSlabT ht hp))
  have hE : Real.sqrt (movingEnergy (-width) width a speed (comparisonCoefficient gRef P z 5)
      (comparisonDifference P z) t) ≤ Real.exp (rate*(b-a))*F*Real.sqrt (2*width)*(b-a) := by
    have hI' : (∫ s in a..t, movingSourceNorm (-width) width a speed
        (metricComparisonSource g gRef P z) s) ≤ F*Real.sqrt (2*width)*(t-a) := by
      simpa only [sub_neg_eq_add,←two_mul] using hI
    have h0 := hEt.trans (mul_le_mul_of_nonneg_left hI' (Real.exp_pos _).le)
    have hexp : Real.exp (rate*(t-a)) ≤ Real.exp (rate*(b-a)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hr)
    have htime : F*Real.sqrt (2*width)*(t-a) ≤ F*Real.sqrt (2*width)*(b-a) :=
      mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) (mul_nonneg hF (Real.sqrt_nonneg _))
    have hprod := mul_le_mul hexp htime
      (mul_nonneg (mul_nonneg hF (Real.sqrt_nonneg _)) (sub_nonneg.mpr ht.1)) (Real.exp_pos _).le
    apply h0.trans
    convert hprod using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | ring
  have hcover : inwardLeft (-width) a speed t ≤ -pulseRadius ∧
      pulseRadius ≤ inwardRight width a speed t := by
    have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hs
    dsimp [inwardLeft,inwardRight]
    constructor <;> linarith
  have hgrad := fixed_slice_gradient_le_moving_energy hW (hWsmooth 5).continuousOn
    ((hz.mono hWV).sub (hP.mono hWV)) hs0 hpulse.le hcover.1 hcover.2
    (fun x hx => hTW (hSlabT ht (point_mem_shrinkingSlab ⟨ht.1,le_rfl⟩ hx)))
    (fun x hx => averagedQCoefficient_lower hgRefV hV
      (hseg _ (hSlabT ht (point_mem_shrinkingSlab ⟨ht.1,le_rfl⟩ hx))) 5
      (fun sigma hsigma => (hmargin _ (hSlabT ht (point_mem_shrinkingSlab ⟨ht.1,le_rfl⟩ hx)) sigma hsigma).2)) i
  exact hgrad.trans (mul_le_mul_of_nonneg_left hE (Real.sqrt_nonneg _))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ActualFiniteShearedCutBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted
open SmoothLocal.HighEquation SmoothLocal.Analytic

theorem exists_actual_finite_sheared_lower_cut_height_bounds
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
          ∀ᶠ tau : ℕ in atTop,
            ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
              SmoothPositiveOn gTau U → IsOpen U →
              (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) →
              (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) →
              CapInductionHeight gTau U Z c e0 z →
              CapInductionFlow gTau U G Z d c e0 kappa z Y W →
              |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
              (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                  testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                    metricApproximationAccuracy tau) →
              ∀ ds : List (Fin 2), ds.length ≤ n → ∀ x : ℝ, |x| ≤ L*r →
                |iteratedCoordPartial ds (heightInShearCoordinates z q0)
                  (coordinatePoint x (-r))| ≤ B := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hcut⟩ := exists_actual_finite_lower_cut_height_bounds
    (e0 := e0) (kappa := kappa) hgStar hV hSV hG hZ hd hc hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro n
  obtain ⟨C,hC,hCn⟩ := hcut n
  refine ⟨(2*(1+|q0|))^n*C, by positivity, ?_⟩
  intro N delta hdelta
  filter_upwards [hCn N delta hdelta] with tau htau
  intro gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox ds hds x hx
  let S : Set Coord := {p | ∃ t : ℝ, |t| ≤ L*r ∧ p = inverseShearCoordinates q0 (boxPoint t (-r))}
  have hSU : S ⊆ U := by
    rintro _ ⟨t,ht,rfl⟩
    exact hf.domainSubset (hf.squareSubset (inverseShear_lower_cut_mem_modelSquare hr hrhalf hLr hq0 ht))
  have hbound : CoordinateBound z S n C := by
    intro es hes _ hp
    obtain ⟨t,ht,rfl⟩ := hp
    exact htau gTau U W z Y hgTau hU hg4 hdet hh hf hcenter happrox es hes t ht
  have hshear := SmoothLocal.Pulse.CoordinateBound.inverse_shear hbound hh.smooth hU hSU hC q0
  exact hshear ds hds (coordinatePoint x (-r)) ⟨x,hx,rfl⟩

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ActualLowMetricFloor
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

theorem exists_actual_determinant_floor_before_pulse_parameters
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) :
    ∃ d : ℝ, 0 < d ∧ (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      ∀ q0 a : ℝ, 0 < a → ∀ N : ℕ, 0 < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop,
          ∀ gTau : MetricField,
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            ∀ p ∈ modelSquare, d ≤ (gTau p).det := by
  obtain ⟨d,epsilon,hd,he,hstar,htol⟩ := exists_metric_value_det_tolerance hgStar hV hSV
  refine ⟨d,hd,hstar,?_⟩
  intro q0 a ha N hN delta
  obtain ⟨tau0,_,herror⟩ := exists_first_error_threshold (by positivity : 0 < 4*epsilon)
  have hehalf : 0 < epsilon/2 := by positivity
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha 0 N hN delta hehalf,
    eventually_ge_atTop tau0] with tau hpulse htau
  intro gTau happ p hp
  apply htol gTau p hp
  intro i j
  have herrorhalf : metricApproximationAccuracy tau ≤ epsilon/2 := by
    have h := herror tau htau
    linarith
  have hE : |gTau p i j-testMetric gStar q0 a N delta (tau : ℝ) p i j| ≤ epsilon/2 := by
    have hzero : |gTau p i j-testMetric gStar q0 a N delta (tau : ℝ) p i j| ≤
        metricApproximationAccuracy tau := by
      simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
        happ i j 0 (Nat.zero_le tau) p hp
    exact hzero.trans herrorhalf
  have hP : |pulseTensor q0 a N delta (tau : ℝ) p i j| ≤ epsilon/2 := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hpulse.2 i j 0 le_rfl p
  have heq : gTau p i j-gStar p i j =
      (gTau p i j-testMetric gStar q0 a N delta (tau : ℝ) p i j)+
        pulseTensor q0 a N delta (tau : ℝ) p i j := by
    change gTau p i j-gStar p i j =
      (gTau p i j-(gStar p i j+pulseTensor q0 a N delta (tau : ℝ) p i j))+
        pulseTensor q0 a N delta (tau : ℝ) p i j
    ring
  rw [heq]
  exact (abs_add_le _ _).trans ((add_le_add hE hP).trans_eq (by ring))

theorem exists_actual_low_metric_data_before_pulse_parameters
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) (m : ℕ) :
    ∃ G d : ℝ, 0 < G ∧ 0 < d ∧
      (∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      (∀ p ∈ modelSquare, d ≤ (gStar p).det) ∧
      ∀ q0 a : ℝ, 0 < a → ∀ N : ℕ, m < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop, m ≤ tau ∧
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            (∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G) ∧
            (∀ p ∈ modelSquare, d ≤ |(gTau p).det|) := by
  obtain ⟨G,hG,hGstar,hjets⟩ := exists_low_metric_budget_before_pulse_parameters hgStar hV hSV m
  obtain ⟨d,hd,hdstar,hfloor⟩ := exists_actual_determinant_floor_before_pulse_parameters hgStar hV hSV
  refine ⟨G,d,hG,hd,hGstar,hdstar,?_⟩
  intro q0 a ha N hmN delta
  filter_upwards [hjets q0 a ha N hmN delta,hfloor q0 a ha N (by omega) delta]
    with tau hjetTau hfloorTau
  refine ⟨hjetTau.1,?_⟩
  intro gTau U hgTau hU hSU happ
  exact ⟨hjetTau.2 gTau U hgTau hU hSU happ,
    fun p hp => (hfloorTau gTau happ p hp).trans (le_abs_self _)⟩

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorRemainderBound
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

theorem qResidual_time_jet_le_fullJet {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    (x t : ℝ) (hx : x ∈ I) (hpU : (![x, t] : Coord) ∈ U)
    (hxx : covHessian g P ![x, t] 0 0 ≠ 0) (N : ℕ) :
    |iteratedDeriv N (fun s => qResidual g P ![x, s]) t| ≤
      ‖iteratedFDeriv ℝ N (qResidual g P) ![x, t]‖ := by
  have hD := comparisonDomain_isOpen hg hU hI hP
  have hR := qResidual_contDiffOn hg hU hI hP
  have hp := mem_comparisonDomain hx hpU hxx
  rw [verticalJet_slice hD hR x N t hp]
  have hb := norm_verticalJet_fullJet_le hR hD hp N 0
  rw [Nat.zero_add, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
  exact hb

end SmoothLocal.Taylor

end

end OAI
end


