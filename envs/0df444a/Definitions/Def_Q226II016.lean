-- Prove2me | Definitions.Def_Q226II016
-- name    : Q226II016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:51:59.050723+00:00
-- url     : https://prove2.me/theorems/d5233464-99b4-4d82-bffc-a9ce62f4f337
-- title:
--   Definitions bundle Q226II016 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 16 declarations of OpenAI's Lean: 16 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`IsometricImmersion_Assembly_SupportedPerturbations`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Assembly/SupportedPerturbations.lean), [`IsometricImmersion_Caps_ActualFiniteCapMetricBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Caps/ActualFiniteCapMetricBounds.lean), [`IsometricImmersion_Caps_BoundedClassReflection`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Caps/BoundedClassReflection.lean), [`IsometricImmersion_Immersions_BoundedHeightClasses`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Immersions/BoundedHeightClasses.lean), [`IsometricImmersion_Metrics_ActualLowMetricBudget`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Metrics/ActualLowMetricBudget.lean), [`IsometricImmersion_Metrics_MetricPatchOpen`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Metrics/MetricPatchOpen.lean), [`IsometricImmersion_Obstructions_PatchObstructionSet`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Obstructions/PatchObstructionSet.lean), [`IsometricImmersion_Obstructions_SmallPatchObstruction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Obstructions/SmallPatchObstruction.lean), [`IsometricImmersion_Taylor_TaylorUpperCauchyBounds`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Taylor/TaylorUpperCauchyBounds.lean), [`IsometricImmersion_Taylor_UniformTaylorDenominator`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/IsometricImmersion/Taylor/UniformTaylorDenominator.lean).
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II012` and `Q226II013` of this split.
--
--   **Imported by** (directly, in this split): the bundle `Q226II018`.
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
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
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
import Mathlib.Topology.GDelta.Basic
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II012
import Definitions.Def_Q226II013

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_SupportedPerturbations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

theorem perturbedMetric_zero (g0 : MetricField) : perturbedMetric g0 0 = g0 := by
  funext p
  change g0 p + 0 = g0 p
  exact add_zero _

theorem zero_mem_metricPatchSet {g0 : MetricField} {kappa : ℝ}
    (hg : ∀ p ∈ modelSquare, (g0 p).PosDef)
    (hK : ∀ p ∈ centralBox, gaussianCurvature g0 p < -kappa / 2) :
    (0 : SymmetricPerturbation) ∈ metricPatchSet g0 kappa := by
  change (∀ p ∈ modelSquare, (perturbedMetric g0 0 p).PosDef) ∧ _
  rw [perturbedMetric_zero]
  exact ⟨hg, hK⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricPatchOpen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Model

theorem metricPatchSet_baire {g0 : MetricField} {U : Set Coord}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) (kappa : ℝ) :
    BaireSpace (metricPatchSet g0 kappa) := by
  let : BaireSpace SymmetricPerturbation := symmetricPerturbation_baire
  exact (metricPatchSet_isOpen hg0 hU hSU kappa).baireSpace

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_ActualFiniteCapMetricBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Flow.Reflection
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

theorem exists_actual_finite_cap_metric_budgets
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V)
    {G Z d c e0 kappa q0 L : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hL : 0 < L) (hq0 : |q0| ≤ 1/20) :
    ∃ r : ℝ, 0 < r ∧ r < 1/2 ∧ L*r ≤ 1/20 ∧
      heightQuotientJetBound G Z d c*(r+107*(L*r)/100) ≤ 9/(100*L) ∧
      ∀ nLower nUpper : ℕ, ∃ B : ℝ, 0 ≤ B ∧
        ∀ N : ℕ, ∀ delta : ℝ, 0 < delta →
          ∀ᶠ tau : ℕ in atTop, finiteCapRequiredMetricOrder nLower nUpper ≤ tau ∧
            ∀ (gTau : MetricField) (U W : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ),
              SmoothPositiveOn gTau U → IsOpen U →
              CapInductionHeight gTau U Z c e0 z →
              CapInductionFlow gTau U G Z d c e0 kappa z Y W →
              |hessianQuotient gTau z 0-q0| ≤ 1/(100*L) →
              (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
                ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                  testMetric gStar q0 (L*r/16) N delta (tau : ℝ) q i j) p‖ ≤
                    metricApproximationAccuracy tau) →
              (∀ R : LowerCapRectangle (-r/2),
                FiniteCapMetricJets gTau Y (fun _ _ => B) (lowerCapPointwiseRequests nLower R)) ∧
              (∀ R : UpperCapRectangle (r/2),
                FiniteUpperCapMetricJets gTau Y (fun _ _ => B) (upperCapPointwiseRequests nUpper R)) := by
  obtain ⟨r,hr,hrhalf,hLr,hrsmall,hsep⟩ :=
    exists_uniform_actual_two_sided_pulse_exclusion (e0 := e0) (kappa := kappa)
      hG hZ hd hc hL hq0
  refine ⟨r,hr,hrhalf,hLr,hrsmall,?_⟩
  intro nLower nUpper
  let m := finiteCapRequiredMetricOrder nLower nUpper
  obtain ⟨Bstar,hBstar,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV m
  refine ⟨Bstar+1,add_nonneg hBstar zero_le_one,?_⟩
  intro N delta hdelta
  filter_upwards [hsep N delta hdelta,eventually_ge_atTop m] with tau htau hm
  refine ⟨hm,?_⟩
  intro gTau U W z Y hgTau hU hh hf hcenter happrox
  obtain ⟨hsepLower,hsepUpper⟩ := htau.2 gTau gStar U W z Y hh hf hcenter
  have herror := metricApproximationAccuracy_le_one htau.1
  have hbound (i j : Fin 2) (k : ℕ) (hk : k ≤ m) (p : Coord) (hpS : p ∈ modelSquare)
      (heq : testMetric gStar q0 (L*r/16) N delta (tau : ℝ) =ᶠ[𝓝 p] gStar) :
      ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ Bstar+1 := by
    have h := metric_jet_norm_le_of_approximation_locality hgStar hgTau hV hU
      (hSV hpS) (hf.domainSubset (hf.squareSubset hpS)) heq i j k
      (hbase i j k hk p hpS) (happrox i j k (hk.trans hm) p hpS)
    exact h.trans (add_le_add le_rfl herror)
  constructor
  · intro R b hb i j k hk p hp
    have hkM : k ≤ m :=
      (lowerCapPointwiseRequests_full_order_le nLower R b hb hk).trans (le_max_left _ _)
    exact hbound i j k hkM p (hf.image_subset_square b.2 hp) (hsepLower b.2 p hp)
  · intro R b hb i j k hk p hp
    have hkM : k ≤ m :=
      (upperCapPointwiseRequests_full_order_le nUpper R b hb hk).trans (le_max_right _ _)
    have hpS : p ∈ modelSquare :=
      (b.2.image_properties (capChart_contDiffOn hf.jointSmooth) hf.displacement).2.2 hp
    exact hbound i j k hkM p hpS (hsepUpper b.2 p hp)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_BoundedHeightClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

theorem every_admissible_height_has_class {g : MetricField} {z : Coord → ℝ}
    (h : PatchAdmissibleHeight g z) (kappa : ℝ) :
    ∃ M : ℕ, BoundedAdmissibleHeight g M z ∧
      ∃ q0 : ℚ, |hessianQuotient g z 0 - (q0 : ℝ)| <
        1 / (100 * boundedClassWidth kappa M) := by
  obtain ⟨M, hM⟩ := h.exists_integer_bound
  obtain ⟨q0, hq0⟩ := exists_rational_bounded_class_label kappa M (hessianQuotient g z 0)
  exact ⟨M, hM, q0, hq0⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_BoundedClassReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Flow.Reflection

theorem reflected_actual_metric_zero_patch {g0 : MetricField} {kappa : ℝ}
    (eta : metricPatchSet g0 kappa) {z : Coord → ℝ} {M : ℕ}
    (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z) :
    (0 : SymmetricPerturbation) ∈
      metricPatchSet (reflectedMetric (perturbedMetric g0 eta.val)) kappa := by
  obtain ⟨U,hU,hSU,hg,hz,hD,hE,hyy,hq⟩ := hclass.2.1
  apply zero_mem_metricPatchSet
  · intro p hp
    exact (reflectedMetric_smoothPositive hg).2 p
      (hSU ((reflectPoint_mem_modelSquare p).mpr hp))
  · intro p hp
    have hpr : reflectPoint p ∈ centralBox :=
      (reflectPoint_mem_symmetricSquare (1/5) p).mpr hp
    rw [reflectedMetric_curvature hg hU (hSU (centralBox_subset_modelSquare hpr))]
    exact eta.property.2 _ hpr

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ActualLowMetricBudget
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem metric_jet_norm_le_from_actual_pulse_approximation
    {gStar gTau : MetricField} {V U : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hgTau : SmoothPositiveOn gTau U)
    (hV : IsOpen V) (hU : IsOpen U) {p : Coord} (hpV : p ∈ V) (hpU : p ∈ U)
    (q0 a : ℝ) (N : ℕ) (delta tau : ℝ) (i j : Fin 2) (k : ℕ) {B P E : ℝ}
    (hbase : ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ B)
    (hpulse : ‖iteratedFDeriv ℝ k (fun q => pulseTensor q0 a N delta tau q i j) p‖ ≤ P)
    (herror : ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
      testMetric gStar q0 a N delta tau q i j) p‖ ≤ E) :
    ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ B+P+E := by
  have hps : ContDiff ℝ ∞ (fun q => pulseTensor q0 a N delta tau q i j) :=
    (contDiff_apply ℝ ℝ j).comp
      ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp (pulseTensor_contDiff q0 a N delta tau))
  have hbs := (hgStar.1 i j).contDiffAt (hV.mem_nhds hpV)
  have hgs := (hgTau.1 i j).contDiffAt (hU.mem_nhds hpU)
  have hts : ContDiffAt ℝ ∞ (fun q => testMetric gStar q0 a N delta tau q i j) p :=
    hbs.add hps.contDiffAt
  have hsplit := iteratedFDeriv_add_apply (i := k)
    (hbs.of_le (WithTop.coe_le_coe.mpr le_top))
    (hps.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  have htest : ‖iteratedFDeriv ℝ k (fun q => testMetric gStar q0 a N delta tau q i j) p‖ ≤ B+P := by
    change ‖iteratedFDeriv ℝ k ((fun q => gStar q i j)+
      (fun q => pulseTensor q0 a N delta tau q i j)) p‖ ≤ _
    rw [hsplit]
    exact (norm_add_le _ _).trans (add_le_add hbase hpulse)
  have hsub := iteratedFDeriv_sub_apply (i := k)
    (hgs.of_le (WithTop.coe_le_coe.mpr le_top))
    (hts.of_le (WithTop.coe_le_coe.mpr le_top))
  change ‖iteratedFDeriv ℝ k ((fun q => gTau q i j)-
    (fun q => testMetric gStar q0 a N delta tau q i j)) p‖ ≤ E at herror
  rw [hsub] at herror
  calc
    _ = ‖(iteratedFDeriv ℝ k (fun q => gTau q i j) p-
          iteratedFDeriv ℝ k (fun q => testMetric gStar q0 a N delta tau q i j) p)+
          iteratedFDeriv ℝ k (fun q => testMetric gStar q0 a N delta tau q i j) p‖ := by
            rw [sub_add_cancel]
    _ ≤ E+(B+P) := (norm_add_le _ _).trans (add_le_add herror htest)
    _ = B+P+E := by ring

theorem exists_low_metric_budget_before_pulse_parameters
    {gStar : MetricField} {V : Set Coord}
    (hgStar : SmoothPositiveOn gStar V) (hV : IsOpen V) (hSV : modelSquare ⊆ V) (m : ℕ) :
    ∃ G : ℝ, 0 < G ∧
      (∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => gStar q i j) p‖ ≤ G) ∧
      ∀ q0 a : ℝ, 0 < a → ∀ N : ℕ, m < N → ∀ delta : ℝ,
        ∀ᶠ tau : ℕ in atTop, m ≤ tau ∧
          ∀ (gTau : MetricField) (U : Set Coord), SmoothPositiveOn gTau U → IsOpen U → modelSquare ⊆ U →
            (∀ i j : Fin 2, ∀ k ≤ tau, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j-
                testMetric gStar q0 a N delta (tau : ℝ) q i j) p‖ ≤ metricApproximationAccuracy tau) →
            ∀ i j : Fin 2, ∀ k ≤ m, ∀ p ∈ modelSquare,
              ‖iteratedFDeriv ℝ k (fun q => gTau q i j) p‖ ≤ G := by
  obtain ⟨B,hB,hbase⟩ := fixed_metric_finite_coefficient_jet_bound hgStar hV hSV m
  refine ⟨B+2,by linarith,?_,?_⟩
  · intro i j k hk p hp
    exact (hbase i j k hk p hp).trans (by linarith)
  intro q0 a ha N hmN delta
  filter_upwards [pulseTensor_finite_coeff_jets_eventually_small q0 a ha m N hmN delta
    (by norm_num : (0 : ℝ)<1),eventually_ge_atTop m] with tau hsmall hmtau
  refine ⟨hmtau,?_⟩
  intro gTau U hgTau hU hSU happ i j k hk p hp
  have hb := metric_jet_norm_le_from_actual_pulse_approximation hgStar hgTau hV hU
    (hSV hp) (hSU hp) q0 a N delta (tau : ℝ) i j k (hbase i j k hk p hp)
      (hsmall.2 i j k hk p) (happ i j k (hk.trans hmtau) p hp)
  exact hb.trans (by linarith [metricApproximationAccuracy_le_one hsmall.1])

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_PatchObstructionSet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

theorem mem_patchObstructionSet_iff {g0 : MetricField} {kappa : ℝ}
    {eta : metricPatchSet g0 kappa} :
    eta ∈ patchObstructionSet g0 kappa ↔
      ∀ M : ℕ, ∀ q0 : ℚ, eta ∉ closure (boundedHeightClass g0 kappa M q0) := by
  simp only [patchObstructionSet, mem_iInter, mem_compl_iff, Prod.forall]

theorem patchObstructionSet_has_no_admissible_height
    {g0 : MetricField} {kappa : ℝ} {eta : metricPatchSet g0 kappa}
    (heta : eta ∈ patchObstructionSet g0 kappa) :
    ∀ z : Coord → ℝ, ¬ PatchAdmissibleHeight (perturbedMetric g0 eta.val) z := by
  intro z hz
  obtain ⟨M,hM,q0,hq0⟩ := every_admissible_height_has_class hz kappa
  have hclass : eta ∈ boundedHeightClass g0 kappa M q0 := ⟨z,hM,hq0⟩
  exact (mem_patchObstructionSet_iff.mp heta M q0) (subset_closure hclass)

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorUpperCauchyBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation
open SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem upper_cauchy_jets_of_actual_coordinate_bound
    {P : Coord → ℝ} {radius a delta tau C : ℝ} {N : ℕ}
    (hP : ContDiffOn ℝ ∞ P (spatialStrip (Ioo (-radius) radius)))
    (ha : a < radius) (ht : 0 ≤ delta/tau)
    (hB : CoordinateBound P (pulseStrip a delta tau) (N+1) C)
    {x : ℝ} (hx : |x| ≤ a) :
    ∀ n ≤ N,
      ‖iteratedFDeriv ℝ n (heightCauchyValue P (delta/tau)) x‖ ≤ C ∧
      ‖iteratedFDeriv ℝ n (heightCauchyVelocity P (delta/tau)) x‖ ≤ C := by
  have hp : coordinatePoint x (delta/tau) ∈ pulseStrip a delta tau := by
    have hp0 : x ∈ Icc (-a) a ∧ delta/tau ∈ Icc (-(delta/tau)) (delta/tau) :=
      ⟨abs_le.mp hx,⟨(neg_nonpos.mpr ht).trans ht,le_rfl⟩⟩
    simpa [coordinatePoint,pulseStrip,SmoothLocal.Weighted.closedRectangle] using hp0
  have hpU : coordinatePoint x (delta/tau) ∈ spatialStrip (Ioo (-radius) radius) := by
    have hxU : x ∈ Ioo (-radius) radius :=
      ⟨(neg_lt_neg ha).trans_le (abs_le.mp hx).1,(abs_le.mp hx).2.trans_lt ha⟩
    simpa [coordinatePoint,spatialStrip] using hxU
  have hval : |P (coordinatePoint x (delta/tau))| ≤ C := hB [] (by simp) _ hp
  have hjet : ∀ i : Fin 2, ∀ n ≤ N,
      |spatialJet (spatialFirstJet P i) n (coordinatePoint x (delta/tau))| ≤ C := by
    intro i n hn
    exact coordinateBound_spatialFirstJet hB hn i hp
  simpa only [max_self] using cauchy_fullJets_of_actual_spatial_firstJets
    hP (spatialStrip_isOpen isOpen_Ioo) hpU hval hjet

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_UniformTaylorDenominator
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

theorem stateQDenominator_uniform_fderiv_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w ∈ stateBaseCompact S M, ‖fderiv ℝ (stateQDenominator g) w‖ ≤ L := by
  have hf := (stateQDenominator_contDiffOn hg hU).continuousOn_fderiv_of_isOpen
    (stateBaseDomain_isOpen hU) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨L, hL⟩ := (stateBaseCompact_isCompact hS M).exists_bound_of_continuousOn
    (hf.mono (fun _ hw => hSU hw.1))
  exact ⟨max L 0, le_max_right _ _, fun w hw => (hL w hw).trans (le_max_left _ _)⟩

theorem qHessian_time_hasDerivAt {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I))
    {x t : ℝ} (hx : x ∈ I) (hp : (![x, t] : Coord) ∈ U) :
    HasDerivAt (fun s => covHessian g P ![x, s] 0 0)
      (fderiv ℝ (stateQDenominator g) (qSolutionJet P ![x, t])
        (fderiv ℝ (qSolutionJet P) ![x, t] (Pi.single 1 1))) t := by
  have hf : DifferentiableAt ℝ (qSolutionJet P) ![x, t] :=
    ((qSolutionJet_contDiffOn (spatialStrip_isOpen hI) hP).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := ((stateQDenominator_contDiffOn hg hU).contDiffAt
    ((stateBaseDomain_isOpen hU).mem_nhds
      (show qSolutionJet P ![x, t] ∈ stateBaseDomain U by
        change statePoint (qSolutionJet P ![x, t]) ∈ U
        rw [statePoint_qSolutionJet]
        exact hp))).differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp_hasDerivAt t
    (hf.hasFDerivAt.comp_hasDerivAt t (verticalPoint_hasDerivAt x t))
  change HasDerivAt (fun s => stateQDenominator g (qSolutionJet P ![x, s]))
    (fderiv ℝ (stateQDenominator g) (qSolutionJet P ![x, t])
      (fderiv ℝ (qSolutionJet P) ![x, t] (Pi.single 1 1))) t at hc
  simp_rw [stateQDenominator_qSolutionJet] at hc
  exact hc

theorem exists_uniform_Hxx_time_variation {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ a t x : ℝ, a ≤ t → x ∈ I →
      (∀ s ∈ Icc a t, (![x, s] : Coord) ∈ S) →
      (∀ s ∈ Icc a t, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j P ![x, s]‖ ≤ R) →
      |covHessian g P ![x, t] 0 0 - covHessian g P ![x, a] 0 0| ≤ L * |t - a| := by
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn (continuousOn_id : ContinuousOn (fun p : Coord => p) S)
  let A0 := max A 0
  have hA0 : 0 ≤ A0 := le_max_right _ _
  have hpoint : ∀ p ∈ S, ‖p‖ ≤ A0 := fun p hp => (hA p hp).trans (le_max_left _ _)
  obtain ⟨L, hL, hder⟩ := stateQDenominator_uniform_fderiv_bound hg hU hS hSU (max A0 R)
  refine ⟨L * max 1 R, mul_nonneg hL (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro P I hI hP a t x hat hx hseg hPB
  have hd (s : ℝ) (hs : s ∈ Icc a t) := qHessian_time_hasDerivAt hg hU hI hP hx (hSU (hseg s hs))
  have hbound (s : ℝ) (hs : s ∈ Icc a t) :
      ‖deriv (fun v => covHessian g P ![x, v] 0 0) s‖ ≤ L * max 1 R := by
    rw [(hd s hs).deriv]
    have hstate := qSolutionJet_norm_bound hP (spatialStrip_isOpen hI) hx hA0 hR
      (hpoint _ (hseg s hs)) (fun j hj => hPB s hs j (by omega))
    have houter := hder (qSolutionJet P ![x, s])
      (stateBaseCompact_mem_of_norm (by simpa only [statePoint_qSolutionJet] using hseg s hs) hstate)
    have hinner : ‖fderiv ℝ (qSolutionJet P) ![x, s]‖ ≤ max 1 R := by
      simpa only [norm_iteratedFDeriv_one] using
        qSolutionJet_positive_fullJet_bound hP (spatialStrip_isOpen hI) hx
          (show 1 ≤ (1 : ℕ) by omega) (fun j hj => hPB s hs j hj)
    have hv : ‖fderiv ℝ (qSolutionJet P) ![x, s] (Pi.single 1 1)‖ ≤ max 1 R := by
      have hv0 : ‖fderiv ℝ (qSolutionJet P) ![x, s] (Pi.single 1 1)‖ ≤
          ‖fderiv ℝ (qSolutionJet P) ![x, s]‖ * ‖(Pi.single 1 1 : Coord)‖ :=
        (fderiv ℝ (qSolutionJet P) ![x, s]).le_opNorm (Pi.single 1 1)
      rw [Pi.norm_single, norm_one, mul_one] at hv0
      exact hv0.trans hinner
    exact ((fderiv ℝ (stateQDenominator g) (qSolutionJet P ![x, s])).le_opNorm _).trans
      (mul_le_mul houter hv (norm_nonneg _) hL)
  have hv := (convex_Icc a t).norm_image_sub_le_of_norm_deriv_le
    (fun s hs => (hd s hs).differentiableAt) hbound
    (show a ∈ Icc a t from ⟨le_rfl, hat⟩) (show t ∈ Icc a t from ⟨hat, le_rfl⟩)
  simpa only [Real.norm_eq_abs] using hv

theorem exists_uniform_Hxx_strip_width {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (R : ℝ) (hR : 0 ≤ R) {c : ℝ} (hc : 0 < c) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧
      ∀ (P : Coord → ℝ) (I : Set ℝ), IsOpen I →
      ContDiffOn ℝ ∞ P (spatialStrip I) → ∀ a t x : ℝ,
      a ≤ t → t - a ≤ epsilon → x ∈ I →
      (∀ s ∈ Icc a t, (![x, s] : Coord) ∈ S) →
      (∀ s ∈ Icc a t, ∀ j ≤ 3, ‖iteratedFDeriv ℝ j P ![x, s]‖ ≤ R) →
      c ≤ |covHessian g P ![x, a] 0 0| → c / 2 ≤ |covHessian g P ![x, t] 0 0| := by
  obtain ⟨L, hL, hvar⟩ := exists_uniform_Hxx_time_variation hg hU hS hSU R hR
  let epsilon := min 1 (c / (2 * (L + 1)))
  have he : 0 < epsilon := lt_min zero_lt_one (div_pos hc (by positivity))
  have hsmall : L * epsilon ≤ c / 2 := by
    have heupper : epsilon ≤ c / (2 * (L + 1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (by positivity : 0 < 2 * (L + 1))).mp heupper
    nlinarith [he.le]
  refine ⟨epsilon, he, min_le_left _ _, ?_⟩
  intro P I hI hP a t x hat htime hx hseg hPB hden
  have hv := hvar P I hI hP a t x hat hx hseg hPB
  rw [abs_of_nonneg (sub_nonneg.mpr hat)] at hv
  have hv' := hv.trans ((mul_le_mul_of_nonneg_left htime hL).trans hsmall)
  rw [abs_sub_comm] at hv'
  have htri : |covHessian g P ![x, a] 0 0| ≤
      |covHessian g P ![x, a] 0 0 - covHessian g P ![x, t] 0 0| +
        |covHessian g P ![x, t] 0 0| := by
    simpa only [sub_add_cancel] using abs_add_le
      (covHessian g P ![x, a] 0 0 - covHessian g P ![x, t] 0 0)
      (covHessian g P ![x, t] 0 0)
  linarith

end SmoothLocal.Taylor

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

theorem model_zero_mem_metricPatchSet
    {g0 : MetricField} {V : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 V) (hSV : modelSquare ⊆ V) (hkappa : 0 < kappa)
    (hbackground : ∀ p ∈ V, gaussianCurvature g0 p=modelCurvature kappa p) :
    (0 : SymmetricPerturbation) ∈ metricPatchSet g0 kappa := by
  apply zero_mem_metricPatchSet
  · intro p hp
    exact hg0.2 p (hSV hp)
  · intro p hp
    rw [hbackground p (hSV (centralBox_subset_modelSquare hp))]
    exact modelCurvature_central_square hkappa (fun i => ⟨hp.1 i,hp.2 i⟩)

end SmoothLocal.Perturbation

end

end OAI
end


