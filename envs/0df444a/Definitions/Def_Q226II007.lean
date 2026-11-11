-- Prove2me | Definitions.Def_Q226II007
-- name    : Q226II007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:42:10.497021+00:00
-- url     : https://prove2.me/theorems/f5710536-6177-475f-aa02-69576fc6ee7f
-- title:
--   Definitions bundle Q226II007 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 185 declarations of OpenAI's Lean: 7 definitions and 178 theorems. The definitions and types are `OAI.SmoothLocal.Flow.capTransportA`, `OAI.SmoothLocal.Flow.capTransportC`, `OAI.SmoothLocal.Flow.heightChartA`, `OAI.SmoothLocal.Flow.heightChartB`, `OAI.SmoothLocal.Flow.heightChartC`, `OAI.SmoothLocal.Flow.heightChartG1`, `OAI.SmoothLocal.Flow.heightChartRemainder`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Calculus_ClosedSquareJetBounds`, `IsometricImmersion_Calculus_CoordinateJetBounds`, `IsometricImmersion_Calculus_HessianCommutator`, `IsometricImmersion_Calculus_HessianJetBounds`, `IsometricImmersion_Calculus_HessianTransport`, `IsometricImmersion_Calculus_MetricInverseJetBounds`, `IsometricImmersion_Calculus_QuotientCalculus`, `IsometricImmersion_Calculus_QuotientLowBounds`, `IsometricImmersion_Calculus_QuotientLowRecurrence`, `IsometricImmersion_Caps_CapAreaFormula`, `IsometricImmersion_Caps_CapDensityBounds`, `IsometricImmersion_Caps_CapFlow`, `IsometricImmersion_Caps_CapFlowCoordinateJets`, `IsometricImmersion_Caps_CapFlowJetBounds`, `IsometricImmersion_Caps_CapFlowUniqueness`, `IsometricImmersion_Caps_CapGradientTransport`, `IsometricImmersion_Caps_CapJacobian`, `IsometricImmersion_Caps_CapReciprocalBounds`, `IsometricImmersion_Caps_EllipticAbsorption`, `IsometricImmersion_Caps_EllipticApplication`, `IsometricImmersion_Caps_EllipticC1`, `IsometricImmersion_Caps_EllipticEnergy`, `IsometricImmersion_Caps_EllipticRatio`, `IsometricImmersion_Caps_IntegratedCapOverlap`, `IsometricImmersion_Caps_PhysicalCapTransport`, `IsometricImmersion_Coordinates_CoordinateFirstBounds`, `IsometricImmersion_Curvature_IntrinsicCurvature`, `IsometricImmersion_Darboux_ActualDriftCoefficients`, `IsometricImmersion_Darboux_ActualDriftEquation`, `IsometricImmersion_Darboux_DarbouxJet`, `IsometricImmersion_Darboux_DriftOperatorIdentity`, `IsometricImmersion_Darboux_HeightPrincipalBounds`, `IsometricImmersion_Darboux_ModelPrincipal`, `IsometricImmersion_Energy_DirectedIntegralEstimate`, `IsometricImmersion_Energy_HeightEnergy`, `IsometricImmersion_Flows_ConstructedHeightFlow`, `IsometricImmersion_Flows_FlowCurvature`, `IsometricImmersion_Flows_FlowExistence`, `IsometricImmersion_Flows_FlowHeightCoefficients`, `IsometricImmersion_Flows_FlowTransport`, `IsometricImmersion_Flows_HeightFlowBoundTools`, `IsometricImmersion_Immersions_HeightCoefficientRegularity`, `IsometricImmersion_Metrics_MetricCompatibility`, `IsometricImmersion_Metrics_MetricLocality`, `IsometricImmersion_Metrics_MetricSmoothness`, `IsometricImmersion_Obstructions_PatchAdmissibility`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II003` and `Q226II004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II011`, `Q226II012` and `Q226II013`.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 334; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II003
import Definitions.Def_Q226II004

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricSmoothness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord}

theorem covHessian_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    {z : Coord → ℝ} (hz : ContDiffOn ℝ ∞ z U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => covHessian g z p i j) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => ∑ k,
      christoffel g k i j p * coordPartial k z p) U := by
    apply ContDiffOn.sum
    intro k hk
    exact (christoffel_contDiffOn hg hU k i j).mul (partial_contDiffOn hz hU k)
  exact (partial_contDiffOn (partial_contDiffOn hz hU j) hU i).sub hs

theorem covectorNormSq_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    {z : Coord → ℝ} (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (covectorNormSq g z) U := by
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact ((inverseMetric_contDiffOn hg i j).mul (partial_contDiffOn hz hU i)).mul
    (partial_contDiffOn hz hU j)

theorem riemann_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (l k i j : Fin 2) :
    ContDiffOn ℝ ∞ (riemann g l k i j) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => ∑ m,
      (christoffel g m j k p * christoffel g l i m p -
        christoffel g m i k p * christoffel g l j m p)) U := by
    apply ContDiffOn.sum
    intro m hm
    exact ((christoffel_contDiffOn hg hU m j k).mul
      (christoffel_contDiffOn hg hU l i m)).sub
        ((christoffel_contDiffOn hg hU m i k).mul
          (christoffel_contDiffOn hg hU l j m))
  exact ((partial_contDiffOn (christoffel_contDiffOn hg hU l j k) hU i).sub
    (partial_contDiffOn (christoffel_contDiffOn hg hU l i k) hU j)).add hs

theorem gaussianCurvature_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (gaussianCurvature g) U := by
  have hn : ContDiffOn ℝ ∞ (fun p => ∑ l, g p 0 l * riemann g l 1 0 1 p) U := by
    apply ContDiffOn.sum
    intro l hl
    exact (hg.1 0 l).mul (riemann_contDiffOn hg hU l 1 0 1)
  exact hn.div (metricDet_contDiffOn hg) (fun p hp => metricDet_ne_zero hg hp)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_HessianCommutator
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem christoffel_lower_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    christoffel g k i j p = christoffel g k j i p := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [metric_coeff_partial_symm hg hU hp l i j]
  ring

theorem covHessian_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (i j : Fin 2) :
    covHessian g z p i j = covHessian g z p j i := by
  unfold covHessian
  rw [coordPartial_comm hz hU hp i j]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [christoffel_lower_symm hg hU hp a i j]

theorem coordPartial_covHessian (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (i j k : Fin 2) :
    coordPartial i (fun q => covHessian g z q j k) p =
      coordPartial i (coordPartial j (coordPartial k z)) p -
        ∑ a, (coordPartial i (christoffel g a j k) p * coordPartial a z p +
          christoffel g a j k p * coordPartial i (coordPartial a z) p) := by
  have hz1 (a : Fin 2) : DifferentiableAt ℝ (coordPartial a z) p :=
    (((partial_contDiffOn hz hU a) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg1 (a : Fin 2) : DifferentiableAt ℝ (christoffel g a j k) p :=
    (((christoffel_contDiffOn hg hU a j k) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hz2 : DifferentiableAt ℝ (coordPartial j (coordPartial k z)) p :=
    (((partial_contDiffOn (partial_contDiffOn hz hU k) hU j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hprod (a : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g a j k q * coordPartial a z q) p :=
    (hg1 a).mul (hz1 a)
  have hsum : DifferentiableAt ℝ
      (fun q => ∑ a, christoffel g a j k q * coordPartial a z q) p := by
    exact DifferentiableAt.fun_sum fun a _ => hprod a
  change coordPartial i (fun q => coordPartial j (coordPartial k z) q -
      ∑ a, christoffel g a j k q * coordPartial a z q) p = _
  rw [HessianCalculus.coordPartial_sub_at hz2 hsum i,
    HessianCalculus.coordPartial_sum_two
      (fun a q => christoffel g a j k q * coordPartial a z q) hprod i]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  exact HessianCalculus.coordPartial_mul_at (hg1 a) (hz1 a) i

theorem covHessian_commutator (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (i j k : Fin 2) :
    covDerivHessian g z i j k p - covDerivHessian g z j i k p =
      -(∑ a, riemann g a k i j p * coordPartial a z p) := by
  have hGamma (a : Fin 2) : christoffel g a i j p = christoffel g a j i p :=
    christoffel_lower_symm hg hU hp a i j
  unfold covDerivHessian
  rw [coordPartial_covHessian hg hU hz hp i j k,
    coordPartial_covHessian hg hU hz hp j i k,
    coordPartial_comm (partial_contDiffOn hz hU k) hU hp i j]
  simp only [covHessian, riemann, Fin.sum_univ_two]
  rw [hGamma 0, hGamma 1]
  ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_QuotientCalculus
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {f h : Coord → ℝ} {p : Coord} {U : Set Coord}

theorem coordinateDrift_quotient (q : Coord → ℝ)
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) :
    coordinateDrift q (fun x => f x / h x) p =
      (coordinateDrift q f p * h p - f p * coordinateDrift q h p) / (h p) ^ 2 := by
  unfold coordinateDrift
  rw [coordPartial_div hf hh hne 0, coordPartial_div hf hh hne 1]
  field_simp [hne]
  ring

theorem coordinateDrift_self_quotient
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) :
    coordinateDrift (fun x => f x / h x) (fun x => f x / h x) p =
      (coordPartial 0 f p - (f p / h p) * coordPartial 1 f p) / h p -
        (f p / h p) *
          (coordPartial 0 h p - (f p / h p) * coordPartial 1 h p) / h p := by
  rw [coordinateDrift_quotient (fun x => f x / h x) hf hh hne]
  unfold coordinateDrift
  field_simp [hne]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_HeightEnergy
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

theorem heightEnergy_contDiffOn {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) :
    ContDiffOn ℝ ∞ (heightEnergy g z) U :=
  (metricDet_contDiffOn hg).mul (contDiffOn_const.sub (covectorNormSq_contDiffOn hg hU hz))

theorem heightEnergy_polynomial {g : MetricField} (z : Coord → ℝ) {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) :
    heightEnergy g z p = (g p).det -
      (g p 1 1 * (coordPartial 0 z p) ^ 2 -
        (g p 0 1 + g p 1 0) * coordPartial 0 z p * coordPartial 1 z p +
        g p 0 0 * (coordPartial 1 z p) ^ 2) := by
  have hdet := metricDet_ne_zero hg hp
  simp only [heightEnergy, covectorNormSq, inverseMetric, Matrix.inv_def,
    Ring.inverse_eq_inv, Matrix.adjugate_fin_two, Fin.sum_univ_two]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [hdet]
  ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open scoped Matrix.Norms.Elementwise
open Filter

namespace SmoothLocal.Geometry

theorem coordPartial_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (i : Fin 2) :
    coordPartial i f =ᶠ[𝓝 p] coordPartial i h := by
  filter_upwards [heq.eventuallyEq_nhds] with q hq
  exact coordPartial_eq_of_eventuallyEq hq i

theorem iteratedCoordPartial_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (dirs : List (Fin 2)) :
    iteratedCoordPartial dirs f =ᶠ[𝓝 p] iteratedCoordPartial dirs h := by
  induction dirs with
  | nil => exact heq
  | cons i is ih => exact coordPartial_eventuallyEq ih i

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_QuotientLowRecurrence
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
namespace LowQuotient

variable {U : Set Coord} {a b : Coord → ℝ} {p : Coord}

theorem product_one (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i : Fin 2) :
    iteratedCoordPartial [i] (fun x => a x * b x) p =
      iteratedCoordPartial [i] a p * b p + a p * iteratedCoordPartial [i] b p :=
  HessianCalculus.coordPartial_mul_at
    (iterated_differentiableAt ha hU hp []) (iterated_differentiableAt hb hU hp []) i

theorem product_two (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i j : Fin 2) :
    iteratedCoordPartial [i, j] (fun x => a x * b x) p =
      iteratedCoordPartial [i, j] a p * b p +
      iteratedCoordPartial [j] a p * iteratedCoordPartial [i] b p +
      iteratedCoordPartial [i] a p * iteratedCoordPartial [j] b p +
      a p * iteratedCoordPartial [i, j] b p := by
  have he : coordPartial j (fun x => a x * b x) =ᶠ[𝓝 p]
      (fun x => coordPartial j a x * b x + a x * coordPartial j b x) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact product_one ha hb hU hx j
  change coordPartial i (coordPartial j (fun x => a x * b x)) p = _
  rw [coordPartial_eq_of_eventuallyEq he i]
  have ha0 := iterated_differentiableAt ha hU hp []
  have hb0 := iterated_differentiableAt hb hU hp []
  have haj := iterated_differentiableAt ha hU hp [j]
  have hbj := iterated_differentiableAt hb hU hp [j]
  have ht0 : DifferentiableAt ℝ (fun x => coordPartial j a x * b x) p := haj.mul hb0
  have ht1 : DifferentiableAt ℝ (fun x => a x * coordPartial j b x) p := ha0.mul hbj
  rw [HessianCalculus.coordPartial_add_at
      (f := fun x => coordPartial j a x * b x) (h := fun x => a x * coordPartial j b x) ht0 ht1 i,
    HessianCalculus.coordPartial_mul_at (f := coordPartial j a) (h := b) haj hb0 i,
    HessianCalculus.coordPartial_mul_at (f := a) (h := coordPartial j b) ha0 hbj i]
  dsimp [iteratedCoordPartial]
  ring

theorem product_three (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] (fun x => a x * b x) p =
      iteratedCoordPartial [i, j, k] a p * b p +
      iteratedCoordPartial [j, k] a p * iteratedCoordPartial [i] b p +
      iteratedCoordPartial [i, k] a p * iteratedCoordPartial [j] b p +
      iteratedCoordPartial [k] a p * iteratedCoordPartial [i, j] b p +
      iteratedCoordPartial [i, j] a p * iteratedCoordPartial [k] b p +
      iteratedCoordPartial [j] a p * iteratedCoordPartial [i, k] b p +
      iteratedCoordPartial [i] a p * iteratedCoordPartial [j, k] b p +
      a p * iteratedCoordPartial [i, j, k] b p := by
  have he : iteratedCoordPartial [j, k] (fun x => a x * b x) =ᶠ[𝓝 p]
      (fun x => iteratedCoordPartial [j, k] a x * b x +
        iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x +
        iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x +
        a x * iteratedCoordPartial [j, k] b x) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact product_two ha hb hU hx j k
  change coordPartial i (iteratedCoordPartial [j, k] (fun x => a x * b x)) p = _
  rw [coordPartial_eq_of_eventuallyEq he i]
  have ha0 := iterated_differentiableAt ha hU hp []
  have hb0 := iterated_differentiableAt hb hU hp []
  have haj := iterated_differentiableAt ha hU hp [j]
  have hak := iterated_differentiableAt ha hU hp [k]
  have hajk := iterated_differentiableAt ha hU hp [j, k]
  have hbj := iterated_differentiableAt hb hU hp [j]
  have hbk := iterated_differentiableAt hb hU hp [k]
  have hbjk := iterated_differentiableAt hb hU hp [j, k]
  have ht0 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x) p := hajk.mul hb0
  have ht1 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x) p := hak.mul hbj
  have ht2 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x) p := haj.mul hbk
  have ht3 : DifferentiableAt ℝ (fun x => a x * iteratedCoordPartial [j, k] b x) p := ha0.mul hbjk
  have ht01 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x +
      iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x) p := ht0.add ht1
  have ht012 : DifferentiableAt ℝ (fun x => iteratedCoordPartial [j, k] a x * b x +
      iteratedCoordPartial [k] a x * iteratedCoordPartial [j] b x +
      iteratedCoordPartial [j] a x * iteratedCoordPartial [k] b x) p := ht01.add ht2
  rw [HessianCalculus.coordPartial_add_at
      ht012 ht3 i,
    HessianCalculus.coordPartial_add_at ht01 ht2 i,
    HessianCalculus.coordPartial_add_at ht0 ht1 i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [j, k] a) (h := b) hajk hb0 i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [k] a) (h := iteratedCoordPartial [j] b) hak hbj i,
    HessianCalculus.coordPartial_mul_at (f := iteratedCoordPartial [j] a) (h := iteratedCoordPartial [k] b) haj hbk i,
    HessianCalculus.coordPartial_mul_at (f := a) (h := iteratedCoordPartial [j, k] b) ha0 hbjk i]
  dsimp [iteratedCoordPartial]
  ring

theorem denominator_mul_quotient_word
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (ds : List (Fin 2)) :
    iteratedCoordPartial ds (fun x => b x * (a x / b x)) p =
      iteratedCoordPartial ds a p := by
  have he : (fun x => b x * (a x / b x)) =ᶠ[𝓝 p] a := by
    filter_upwards [hU.mem_nhds hp] with x hx
    field_simp [hne x hx]
  exact (iteratedCoordPartial_eventuallyEq he ds).self_of_nhds

theorem quotient_one (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i : Fin 2) :
    iteratedCoordPartial [i] (fun x => a x / b x) p =
      (iteratedCoordPartial [i] a p -
        iteratedCoordPartial [i] b p * (a p / b p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i]
  rw [product_one hb (quotient_contDiffOn ha hb hne) hU hp i] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

theorem quotient_two (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i j : Fin 2) :
    iteratedCoordPartial [i, j] (fun x => a x / b x) p =
      (iteratedCoordPartial [i, j] a p -
        (iteratedCoordPartial [i, j] b p * (a p / b p) +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j] (fun x => a x / b x) p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i, j]
  rw [product_two hb (quotient_contDiffOn ha hb hne) hU hp i j] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

theorem quotient_three (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hU : IsOpen U) (hp : p ∈ U) (hne : ∀ x ∈ U, b x ≠ 0) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] (fun x => a x / b x) p =
      (iteratedCoordPartial [i, j, k] a p -
        (iteratedCoordPartial [i, j, k] b p * (a p / b p) +
        iteratedCoordPartial [j, k] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i, k] b p * iteratedCoordPartial [j] (fun x => a x / b x) p +
        iteratedCoordPartial [k] b p * iteratedCoordPartial [i, j] (fun x => a x / b x) p +
        iteratedCoordPartial [i, j] b p * iteratedCoordPartial [k] (fun x => a x / b x) p +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i, k] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j, k] (fun x => a x / b x) p)) / b p := by
  have he := denominator_mul_quotient_word (a := a) hU hp hne [i, j, k]
  rw [product_three hb (quotient_contDiffOn ha hb hne) hU hp i j k] at he
  apply (eq_div_iff (hne p hp)).2
  nlinarith [he]

end LowQuotient
end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_QuotientLowBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.LowQuotient

variable {U : Set Coord} {a b : Coord → ℝ} {M c : ℝ}

section SmoothQuotient
variable (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U) (hU : IsOpen U)
variable (hM : 0 ≤ M) (hc : 0 < c)
variable (haB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds a p| ≤ M)
variable (hbB : ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U, |iteratedCoordPartial ds b p| ≤ M)
variable (hden : ∀ p ∈ U, c ≤ |b p|)
include ha hb hU hM hc haB hbB hden

theorem quotient_bound_one {p : Coord} (hp : p ∈ U) (i : Fin 2) :
    |iteratedCoordPartial [i] (fun x => a x / b x) p| ≤ bound1 M c := by
  rw [quotient_one ha hb hU hp (denominator_ne_zero hc hden) i]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  apply abs_div_bound (by have := (bounds_nonneg hM hc).1; positivity) _ hc (hden p hp)
  exact abs_sub_bound (haB [i] (by norm_num) p hp)
    (abs_mul_bound (hbB [i] (by norm_num) p hp) hq0 hM)

theorem quotient_bound_two {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    |iteratedCoordPartial [i, j] (fun x => a x / b x) p| ≤ bound2 M c := by
  rw [quotient_two ha hb hU hp (denominator_ne_zero hc hden) i j]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  have hqi := quotient_bound_one ha hb hU hM hc haB hbB hden hp i
  have hqj := quotient_bound_one ha hb hU hM hc haB hbB hden hp j
  have hterm0 := abs_mul_bound (hbB [i, j] (by norm_num) p hp) hq0 hM
  have htermi := abs_mul_bound (hbB [j] (by norm_num) p hp) hqi hM
  have htermj := abs_mul_bound (hbB [i] (by norm_num) p hp) hqj hM
  have hrest := abs_add_bound (abs_add_bound hterm0 htermi) htermj
  have hnum := abs_sub_bound (haB [i, j] (by norm_num) p hp) hrest
  have hnum' :
      |iteratedCoordPartial [i, j] a p -
        (iteratedCoordPartial [i, j] b p * (a p / b p) +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j] (fun x => a x / b x) p)| ≤
        M + M * bound0 M c + 2 * M * bound1 M c := by
    convert hnum using 1 <;> first | rfl | ring
  exact abs_div_bound (by obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc; positivity)
    hnum' hc (hden p hp)

theorem quotient_bound_three {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    |iteratedCoordPartial [i, j, k] (fun x => a x / b x) p| ≤ bound3 M c := by
  rw [quotient_three ha hb hU hp (denominator_ne_zero hc hden) i j k]
  have hq0 := quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp
  have hqi := quotient_bound_one ha hb hU hM hc haB hbB hden hp i
  have hqj := quotient_bound_one ha hb hU hM hc haB hbB hden hp j
  have hqk := quotient_bound_one ha hb hU hM hc haB hbB hden hp k
  have hqij := quotient_bound_two ha hb hU hM hc haB hbB hden hp i j
  have hqik := quotient_bound_two ha hb hU hM hc haB hbB hden hp i k
  have hqjk := quotient_bound_two ha hb hU hM hc haB hbB hden hp j k
  have h0 := abs_mul_bound (hbB [i, j, k] (by norm_num) p hp) hq0 hM
  have h1 := abs_mul_bound (hbB [j, k] (by norm_num) p hp) hqi hM
  have h2 := abs_mul_bound (hbB [i, k] (by norm_num) p hp) hqj hM
  have h3 := abs_mul_bound (hbB [k] (by norm_num) p hp) hqij hM
  have h4 := abs_mul_bound (hbB [i, j] (by norm_num) p hp) hqk hM
  have h5 := abs_mul_bound (hbB [j] (by norm_num) p hp) hqik hM
  have h6 := abs_mul_bound (hbB [i] (by norm_num) p hp) hqjk hM
  have hrest := abs_add_bound (abs_add_bound (abs_add_bound (abs_add_bound
    (abs_add_bound (abs_add_bound h0 h1) h2) h3) h4) h5) h6
  have hnum := abs_sub_bound (haB [i, j, k] (by norm_num) p hp) hrest
  have hnum' :
      |iteratedCoordPartial [i, j, k] a p -
        (iteratedCoordPartial [i, j, k] b p * (a p / b p) +
        iteratedCoordPartial [j, k] b p * iteratedCoordPartial [i] (fun x => a x / b x) p +
        iteratedCoordPartial [i, k] b p * iteratedCoordPartial [j] (fun x => a x / b x) p +
        iteratedCoordPartial [k] b p * iteratedCoordPartial [i, j] (fun x => a x / b x) p +
        iteratedCoordPartial [i, j] b p * iteratedCoordPartial [k] (fun x => a x / b x) p +
        iteratedCoordPartial [j] b p * iteratedCoordPartial [i, k] (fun x => a x / b x) p +
        iteratedCoordPartial [i] b p * iteratedCoordPartial [j, k] (fun x => a x / b x) p)| ≤
        M + M * bound0 M c + 3 * M * bound1 M c + 3 * M * bound2 M c := by
    convert hnum using 1 <;> first | rfl | ring
  exact abs_div_bound (by obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc; positivity)
    hnum' hc (hden p hp)

theorem quotient_bound_through_three (ds : List (Fin 2)) (hlen : ds.length ≤ 3)
    {p : Coord} (hp : p ∈ U) :
    |iteratedCoordPartial ds (fun x => a x / b x) p| ≤ boundThroughThree M c := by
  obtain ⟨h0, h1, h2, h3⟩ := bounds_nonneg hM hc
  have hB0 : bound0 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree] <;> linarith
  have hB1 : bound1 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree] <;> linarith
  have hB2 : bound2 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree] <;> linarith
  have hB3 : bound3 M c ≤ boundThroughThree M c := by dsimp [boundThroughThree] <;> linarith
  cases ds with
  | nil => exact (quotient_bound_zero hM hc (haB [] (by norm_num)) hden hp).trans hB0
  | cons i ds =>
    cases ds with
    | nil => exact (quotient_bound_one ha hb hU hM hc haB hbB hden hp i).trans hB1
    | cons j ds =>
      cases ds with
      | nil => exact (quotient_bound_two ha hb hU hM hc haB hbB hden hp i j).trans hB2
      | cons k ds =>
        cases ds with
        | nil => exact (quotient_bound_three ha hb hU hM hc haB hbB hden hp i j k).trans hB3
        | cons l ds => simp only [List.length_cons] at hlen; omega

end SmoothQuotient
end SmoothLocal.Geometry.LowQuotient

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricCompatibility
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem metricDet_coordPartial (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (fun q => (g q).det) p =
      coordPartial k (fun q => g q 0 0) p * g p 1 1 +
        g p 0 0 * coordPartial k (fun q => g q 1 1) p -
        (coordPartial k (fun q => g q 0 1) p * g p 1 0 +
          g p 0 1 * coordPartial k (fun q => g q 1 0) p) := by
  have hd (i j : Fin 2) : DifferentiableAt ℝ (fun q => g q i j) p :=
    (((hg.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  simp only [Matrix.det_fin_two]
  have hprod₀ : DifferentiableAt ℝ (fun q => g q 0 0 * g q 1 1) p :=
    (hd 0 0).mul (hd 1 1)
  have hprod₁ : DifferentiableAt ℝ (fun q => g q 0 1 * g q 1 0) p :=
    (hd 0 1).mul (hd 1 0)
  rw [HessianCalculus.coordPartial_sub_at hprod₀ hprod₁ k,
    HessianCalculus.coordPartial_mul_at (hd 0 0) (hd 1 1) k,
    HessianCalculus.coordPartial_mul_at (hd 0 1) (hd 1 0) k]

theorem metricDet_partial_trace (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (fun q => (g q).det) p =
      2 * (christoffel g 0 k 0 p + christoffel g 1 k 1 p) * (g p).det := by
  rw [metricDet_coordPartial hg hU hp k]
  simp only [metric_compatibility hg hU hp, Fin.sum_univ_two, Matrix.det_fin_two]
  ring

theorem heightEnergy_polynomial_symm (z : Coord → ℝ)
    (hg : SmoothPositiveOn g U) (hp : p ∈ U) :
    heightEnergy g z p = (g p).det -
      (g p 1 1 * (coordPartial 0 z p) ^ 2 -
        2 * g p 0 1 * coordPartial 0 z p * coordPartial 1 z p +
        g p 0 0 * (coordPartial 1 z p) ^ 2) := by
  rw [heightEnergy_polynomial z hg hp, metric_coeff_symm hg hp 1 0]
  ring

theorem coordPartial_heightEnergy_polynomial
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (heightEnergy g z) p =
      coordPartial k (fun q => (g q).det) p -
        (coordPartial k (fun q => g q 1 1) p * (coordPartial 0 z p) ^ 2 +
          2 * g p 1 1 * coordPartial 0 z p * coordPartial k (coordPartial 0 z) p -
          (2 * coordPartial k (fun q => g q 0 1) p * coordPartial 0 z p * coordPartial 1 z p +
            2 * g p 0 1 * coordPartial k (coordPartial 0 z) p * coordPartial 1 z p +
            2 * g p 0 1 * coordPartial 0 z p * coordPartial k (coordPartial 1 z) p) +
          coordPartial k (fun q => g q 0 0) p * (coordPartial 1 z p) ^ 2 +
          2 * g p 0 0 * coordPartial 1 z p * coordPartial k (coordPartial 1 z) p) := by
  have heq : heightEnergy g z =ᶠ[𝓝 p] (fun q => (g q).det -
      (g q 1 1 * (coordPartial 0 z q) ^ 2 -
        2 * g q 0 1 * coordPartial 0 z q * coordPartial 1 z q +
        g q 0 0 * (coordPartial 1 z q) ^ 2)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact heightEnergy_polynomial_symm z hg hq
  have hdg (i j : Fin 2) : DifferentiableAt ℝ (fun q => g q i j) p :=
    (((hg.1 i j) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdz (i : Fin 2) : DifferentiableAt ℝ (coordPartial i z) p :=
    (((partial_contDiffOn hz hU i) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdet : DifferentiableAt ℝ (fun q => (g q).det) p :=
    (((metricDet_contDiffOn hg) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hquad : DifferentiableAt ℝ (fun q =>
      g q 1 1 * (coordPartial 0 z q) ^ 2 -
        2 * g q 0 1 * coordPartial 0 z q * coordPartial 1 z q +
        g q 0 0 * (coordPartial 1 z q) ^ 2) p :=
    (((hdg 1 1).mul ((hdz 0).pow 2)).sub
      ((((hdg 0 1).const_mul (2 : ℝ)).mul (hdz 0)).mul (hdz 1))).add
        ((hdg 0 0).mul ((hdz 1).pow 2))
  change fderiv ℝ (heightEnergy g z) p (Pi.single k 1) = _
  rw [heq.fderiv_eq]
  change coordPartial k (fun q => (g q).det -
      (g q 1 1 * (coordPartial 0 z q) ^ 2 -
        2 * g q 0 1 * coordPartial 0 z q * coordPartial 1 z q +
        g q 0 0 * (coordPartial 1 z q) ^ 2)) p = _
  rw [HessianCalculus.coordPartial_sub_at hdet hquad k,
    CompatibilityCalculus.coordPartial_quadratic
      (hdg 1 1) (hdg 0 1) (hdg 0 0) (hdz 0) (hdz 1) k]

theorem coordPartial_heightEnergy
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (k : Fin 2) :
    coordPartial k (heightEnergy g z) p =
      2 * (christoffel g 0 k 0 p + christoffel g 1 k 1 p) * heightEnergy g z p -
        2 * (covHessian g z p k 0 *
            (g p 1 1 * coordPartial 0 z p - g p 0 1 * coordPartial 1 z p) +
          covHessian g z p k 1 *
            (g p 0 0 * coordPartial 1 z p - g p 0 1 * coordPartial 0 z p)) := by
  rw [coordPartial_heightEnergy_polynomial hg hU hz hp k,
    metricDet_partial_trace hg hU hp k, heightEnergy_polynomial_symm z hg hp]
  simp only [metric_compatibility hg hU hp, covHessian, Fin.sum_univ_two,
    Matrix.det_fin_two]
  rw [metric_coeff_symm hg hp 1 0]
  ring

theorem heightEnergy_y_quotient
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    coordPartial 1 (heightEnergy g z) p =
      2 * (christoffel g 0 0 1 p + christoffel g 1 1 1 p) * heightEnergy g z p -
        2 * covHessian g z p 1 1 *
          ((g p 0 0 - (covHessian g z p 0 1 / covHessian g z p 1 1) * g p 0 1) *
              coordPartial 1 z p -
            (g p 0 1 - (covHessian g z p 0 1 / covHessian g z p 1 1) * g p 1 1) *
              coordPartial 0 z p) := by
  rw [coordPartial_heightEnergy hg hU hz hp 1,
    christoffel_lower_symm hg hU hp 0 1 0,
    covHessian_symm hg hU hz hp 1 0]
  field_simp [hyy]
  ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_ActualDriftCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem hessianQuotient_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U :=
  (covHessian_contDiffOn hg hU hz 0 1).div (covHessian_contDiffOn hg hU hz 1 1) hyy

theorem darbouxG_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (darbouxG g z) U :=
  (heightEnergy_contDiffOn hg hU hz).div ((covHessian_contDiffOn hg hU hz 1 1).pow 2)
    (fun p hp => pow_ne_zero 2 (hyy p hp))

theorem connectionTraceY_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (connectionTraceY g) U :=
  (christoffel_contDiffOn hg hU 0 0 1).add (christoffel_contDiffOn hg hU 1 1 1)

theorem driftJ_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (driftJ g z) U := by
  have hq := hessianQuotient_contDiffOn hg hU hz hyy
  exact (((hg.1 0 0).sub (hq.mul (hg.1 0 1))).mul (partial_contDiffOn hz hU 1)).sub
    (((hg.1 0 1).sub (hq.mul (hg.1 1 1))).mul (partial_contDiffOn hz hU 0))

theorem curvatureDriftError_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (curvatureDriftError g z) U :=
  explicitDriftError_contDiffOn hU (covHessian_contDiffOn hg hU hz 1 1)
    (heightEnergy_contDiffOn hg hU hz) (connectionTraceY_contDiffOn hg hU)
    (driftJ_contDiffOn hg hU hz hyy) hyy

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_CoordinateJetBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

namespace CoordinateBound

theorem iterated_add {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun x => f x + h x) p =
      iteratedCoordPartial ds f p + iteratedCoordPartial ds h p := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (fun x => f x + h x) =ᶠ[𝓝 p]
        (fun x => iteratedCoordPartial ds f x + iteratedCoordPartial ds h x) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds (fun x => f x + h x)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    exact HessianCalculus.coordPartial_add_at
      (LowQuotient.iterated_differentiableAt hf hU hp ds)
      (LowQuotient.iterated_differentiableAt hh hU hp ds) i

theorem iterated_sub {f h : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun x => f x - h x) p =
      iteratedCoordPartial ds f p - iteratedCoordPartial ds h p := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (fun x => f x - h x) =ᶠ[𝓝 p]
        (fun x => iteratedCoordPartial ds f x - iteratedCoordPartial ds h x) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds (fun x => f x - h x)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    exact HessianCalculus.coordPartial_sub_at
      (LowQuotient.iterated_differentiableAt hf hU hp ds)
      (LowQuotient.iterated_differentiableAt hh hU hp ds) i

theorem iterated_const_mul {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (c : ℝ)
    (ds : List (Fin 2)) {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds (fun x => c * f x) p = c * iteratedCoordPartial ds f p := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds (fun x => c * f x) =ᶠ[𝓝 p]
        (fun x => c * iteratedCoordPartial ds f x) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds (fun x => c * f x)) p = _
    rw [coordPartial_eq_of_eventuallyEq he i,
      HessianCalculus.coordPartial_mul_at (f := fun _ : Coord => c) (h := iteratedCoordPartial ds f)
        (differentiableAt_const c)
        (LowQuotient.iterated_differentiableAt hf hU hp ds) i]
    simp [coordPartial, iteratedCoordPartial]

theorem add {f h : Coord → ℝ} {U : Set Coord} {n : ℕ} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hfB : CoordinateBound f U n A) (hhB : CoordinateBound h U n B) :
    CoordinateBound (fun x => f x + h x) U n (A + B) := by
  intro ds hds p hp
  rw [iterated_add hf hh hU ds hp]
  exact (abs_add_le _ _).trans (add_le_add (hfB ds hds p hp) (hhB ds hds p hp))

theorem sub {f h : Coord → ℝ} {U : Set Coord} {n : ℕ} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hfB : CoordinateBound f U n A) (hhB : CoordinateBound h U n B) :
    CoordinateBound (fun x => f x - h x) U n (A + B) := by
  intro ds hds p hp
  rw [iterated_sub hf hh hU ds hp]
  exact (abs_sub _ _).trans (add_le_add (hfB ds hds p hp) (hhB ds hds p hp))

theorem const_mul {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {A : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hfB : CoordinateBound f U n A) (c : ℝ) :
    CoordinateBound (fun x => c * f x) U n (|c| * A) := by
  intro ds hds p hp
  rw [iterated_const_mul hf hU c ds hp, abs_mul]
  exact mul_le_mul_of_nonneg_left (hfB ds hds p hp) (abs_nonneg c)

theorem neg {f : Coord → ℝ} {U : Set Coord} {n : ℕ} {A : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hfB : CoordinateBound f U n A) :
    CoordinateBound (fun x => -f x) U n A := by
  simpa only [neg_one_mul, abs_neg, abs_one, one_mul] using const_mul hf hU hfB (-1)

theorem mul_through_three {f h : Coord → ℝ} {U : Set Coord} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfB : CoordinateBound f U 3 A) (hhB : CoordinateBound h U 3 B) :
    CoordinateBound (fun x => f x * h x) U 3 (8 * A * B) := by
  intro ds hds p hp
  have hab (vs ws : List (Fin 2)) (hv : vs.length ≤ 3) (hw : ws.length ≤ 3) :
      |iteratedCoordPartial vs f p * iteratedCoordPartial ws h p| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (hfB vs hv p hp) (hhB ws hw p hp) (abs_nonneg _) hA
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  cases ds with
  | nil =>
    exact (hab [] [] (by norm_num) (by norm_num)).trans (by nlinarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.product_one hf hh hU hp i]
      exact (abs_add_bound (hab [i] [] (by norm_num) (by norm_num))
        (hab [] [i] (by norm_num) (by norm_num))).trans (by nlinarith)
    | cons j ds =>
      cases ds with
      | nil =>
        rw [LowQuotient.product_two hf hh hU hp i j]
        exact (abs_add_bound (abs_add_bound (abs_add_bound
          (hab [i, j] [] (by norm_num) (by norm_num))
          (hab [j] [i] (by norm_num) (by norm_num)))
          (hab [i] [j] (by norm_num) (by norm_num)))
          (hab [] [i, j] (by norm_num) (by norm_num))).trans (by nlinarith)
      | cons k ds =>
        cases ds with
        | nil =>
          rw [LowQuotient.product_three hf hh hU hp i j k]
          have hsum := abs_add_bound (abs_add_bound (abs_add_bound (abs_add_bound
            (abs_add_bound (abs_add_bound (abs_add_bound
            (hab [i, j, k] [] (by norm_num) (by norm_num))
            (hab [j, k] [i] (by norm_num) (by norm_num)))
            (hab [i, k] [j] (by norm_num) (by norm_num)))
            (hab [k] [i, j] (by norm_num) (by norm_num)))
            (hab [i, j] [k] (by norm_num) (by norm_num)))
            (hab [j] [i, k] (by norm_num) (by norm_num)))
            (hab [i] [j, k] (by norm_num) (by norm_num)))
            (hab [] [i, j, k] (by norm_num) (by norm_num))
          convert hsum using 1 <;> first | rfl | ring
        | cons l ds => simp only [List.length_cons] at hds; omega

end CoordinateBound
end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MetricInverseJetBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord} {G d : ℝ}

theorem metricDet_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G) :
    CoordinateBound (fun p => (g p).det) U 3 (16 * G^2) := by
  have hdiag := CoordinateBound.mul_through_three (hg.1 0 0) (hg.1 1 1) hU hG hG (hgB 0 0) (hgB 1 1)
  have hoff := CoordinateBound.mul_through_three (hg.1 0 1) (hg.1 1 0) hU hG hG (hgB 0 1) (hgB 1 0)
  have hdet := CoordinateBound.sub ((hg.1 0 0).mul (hg.1 1 1))
    ((hg.1 0 1).mul (hg.1 1 0)) hU hdiag hoff
  have hc : 8 * G * G + 8 * G * G = 16 * G^2 := by ring
  simpa only [Matrix.det_fin_two, hc] using hdet

theorem metricAdjugate_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G) (i j : Fin 2) :
    CoordinateBound (fun p => (g p).adjugate i j) U 3 G := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using hgB 1 1
  · simpa [Matrix.adjugate_fin_two] using CoordinateBound.neg (hg.1 0 1) hU (hgB 0 1)
  · simpa [Matrix.adjugate_fin_two] using CoordinateBound.neg (hg.1 1 0) hU (hgB 1 0)
  · simpa [Matrix.adjugate_fin_two] using hgB 0 0

theorem inverseMetric_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (i j : Fin 2) :
    CoordinateBound (fun p => inverseMetric g p i j) U 3 (metricInverseJetBound G d) := by
  have hN : 0 ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound] <;> positivity
  have hGN : G ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound] <;> nlinarith [sq_nonneg G]
  have hDN : 16 * G^2 ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound] <;> linarith
  have hadj := (metricAdjugate_coordinate_bound hg hU hgB i j).mono le_rfl hGN
  have hdetB := (metricDet_coordinate_bound hg hU hG hgB).mono le_rfl hDN
  rw [inverseMetric_eq_adjugate_div]
  intro ds hds p hp
  exact LowQuotient.quotient_bound_through_three (metricAdjugate_contDiffOn hg i j)
    (metricDet_contDiffOn hg) hU hN hd hadj hdetB hdet ds hds hp

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_HessianJetBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem connectionBracket_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (i j l : Fin 2) : ContDiffOn ℝ ∞ (connectionBracket g i j l) U :=
  ((partial_contDiffOn (hg.1 j l) hU i).add
    (partial_contDiffOn (hg.1 i l) hU j)).sub (partial_contDiffOn (hg.1 i j) hU l)

theorem connectionBracket_coordinate_bound (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G) (i j l : Fin 2) :
    CoordinateBound (connectionBracket g i j l) U 3 (3 * G) := by
  have h1 : CoordinateBound (coordPartial i (fun p => g p j l)) U 3 G := (hgB j l).partial_bound i
  have h2 : CoordinateBound (coordPartial j (fun p => g p i l)) U 3 G := (hgB i l).partial_bound j
  have h3 : CoordinateBound (coordPartial l (fun p => g p i j)) U 3 G := (hgB i j).partial_bound l
  have hb := CoordinateBound.sub
    ((partial_contDiffOn (hg.1 j l) hU i).add (partial_contDiffOn (hg.1 i l) hU j))
    (partial_contDiffOn (hg.1 i j) hU l) hU
    (CoordinateBound.add (partial_contDiffOn (hg.1 j l) hU i)
      (partial_contDiffOn (hg.1 i l) hU j) hU h1 h2) h3
  have he : G + G + G = 3 * G := by ring
  rw [he] at hb
  exact hb

theorem christoffel_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (k i j : Fin 2) :
    CoordinateBound (christoffel g k i j) U 3 (christoffelJetBound G d) := by
  have hg3 (a b : Fin 2) : CoordinateBound (fun p => g p a b) U 3 G :=
    (hgB a b).mono (by norm_num) le_rfl
  have hI := metricInverseJetBound_nonneg hG hd
  have hprod (l : Fin 2) : CoordinateBound
      (fun p => inverseMetric g p k l * connectionBracket g i j l p) U 3
      (8 * metricInverseJetBound G d * (3 * G)) :=
    CoordinateBound.mul_through_three (inverseMetric_contDiffOn hg k l)
      (connectionBracket_contDiffOn hg hU i j l) hU hI (by positivity)
      (inverseMetric_coordinate_bound hg hU hG hd hg3 hdet k l)
      (connectionBracket_coordinate_bound hg hU hgB i j l)
  have hs := CoordinateBound.add
    ((inverseMetric_contDiffOn hg k 0).mul (connectionBracket_contDiffOn hg hU i j 0))
    ((inverseMetric_contDiffOn hg k 1).mul (connectionBracket_contDiffOn hg hU i j 1))
    hU (hprod 0) (hprod 1)
  have hhalf := CoordinateBound.const_mul
    (((inverseMetric_contDiffOn hg k 0).mul (connectionBracket_contDiffOn hg hU i j 0)).add
      ((inverseMetric_contDiffOn hg k 1).mul (connectionBracket_contDiffOn hg hU i j 1)))
    hU hs (1 / 2 : ℝ)
  have hc : |(1 / 2 : ℝ)| *
      (8 * metricInverseJetBound G d * (3 * G) + 8 * metricInverseJetBound G d * (3 * G)) =
      christoffelJetBound G d := by
    norm_num [christoffelJetBound]
    ring
  rw [hc] at hhalf
  convert hhalf using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  simp only [christoffel, Fin.sum_univ_two, connectionBracket]

theorem covHessian_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (i j : Fin 2) :
    CoordinateBound (fun p => covHessian g z p i j) U 3 (hessianJetBound G Z d) := by
  have hz4 (a : Fin 2) : CoordinateBound (coordPartial a z) U 4 Z := hzB.partial_bound a
  have hz1 (a : Fin 2) : CoordinateBound (coordPartial a z) U 3 Z :=
    (hz4 a).mono (by norm_num) le_rfl
  have hz2 : CoordinateBound (coordPartial i (coordPartial j z)) U 3 Z := (hz4 j).partial_bound i
  have hΓ := christoffelJetBound_nonneg hG hd
  have hprod (a : Fin 2) : CoordinateBound
      (fun p => christoffel g a i j p * coordPartial a z p) U 3
      (8 * christoffelJetBound G d * Z) :=
    CoordinateBound.mul_through_three (christoffel_contDiffOn hg hU a i j)
      (partial_contDiffOn hz hU a) hU hΓ hZ
      (christoffel_coordinate_bound hg hU hG hd hgB hdet a i j) (hz1 a)
  have hs := CoordinateBound.add
    ((christoffel_contDiffOn hg hU 0 i j).mul (partial_contDiffOn hz hU 0))
    ((christoffel_contDiffOn hg hU 1 i j).mul (partial_contDiffOn hz hU 1))
    hU (hprod 0) (hprod 1)
  have hh := CoordinateBound.sub (partial_contDiffOn (partial_contDiffOn hz hU j) hU i)
    (((christoffel_contDiffOn hg hU 0 i j).mul (partial_contDiffOn hz hU 0)).add
      ((christoffel_contDiffOn hg hU 1 i j).mul (partial_contDiffOn hz hU 1))) hU hz2 hs
  have hc : Z + (8 * christoffelJetBound G d * Z + 8 * christoffelJetBound G d * Z) =
      hessianJetBound G Z d := by dsimp [hessianJetBound] <;> ring
  simpa only [covHessian, Fin.sum_univ_two, hc] using hh

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_IntrinsicCurvature
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord} {p : Coord}

theorem riemann_factorization (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    riemann g l k i j p = gaussianCurvature g p * curvatureFactor g l k i j p := by
  have hvec :
      g p *ᵥ (fun r => riemann g r k i j p) =
      g p *ᵥ (fun r => gaussianCurvature g p * curvatureFactor g r k i j p) := by
    ext a
    change loweredRiemann g a k i j p =
      ∑ r, g p a r * (gaussianCurvature g p * curvatureFactor g r k i j p)
    rw [loweredRiemann_factorization hg hU hp]
    fin_cases i <;> fin_cases j <;> simp [curvatureFactor, Fin.sum_univ_two] <;> ring
  have h := Matrix.mulVec_injective_of_isUnit (hg.2 p hp).isUnit hvec
  exact congrFun h l

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_HessianTransport
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem covHessian_coordPartial_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) (d i j : Fin 2) :
    coordPartial d (fun q => covHessian g z q i j) p =
      coordPartial d (fun q => covHessian g z q j i) p := by
  have heq : (fun q => covHessian g z q i j) =ᶠ[𝓝 p]
      (fun q => covHessian g z q j i) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact covHessian_symm hg hU hz hq i j
  unfold coordPartial
  rw [heq.fderiv_eq]

theorem hessian_transport_Ay_Bx
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) :
    coordPartial 1 (fun q => covHessian g z q 0 0) p -
        coordPartial 0 (fun q => covHessian g z q 0 1) p =
      christoffel g 0 0 1 p * covHessian g z p 0 0 +
        (christoffel g 1 0 1 p - christoffel g 0 0 0 p) * covHessian g z p 0 1 -
        christoffel g 1 0 0 p * covHessian g z p 1 1 +
        gaussianCurvature g p * (g p 0 1 * coordPartial 0 z p -
          g p 0 0 * coordPartial 1 z p) := by
  have hc := covHessian_commutator hg hU hz hp 0 1 0
  simp only [covDerivHessian, Fin.sum_univ_two, riemann_factorization hg hU hp] at hc
  simp [curvatureFactor] at hc
  simp only [covHessian_coordPartial_symm hg hU hz hp 0 1 0,
    covHessian_symm hg hU hz hp 1 0,
    christoffel_lower_symm hg hU hp 0 1 0,
    christoffel_lower_symm hg hU hp 1 1 0,
    metric_coeff_symm hg hp 1 0] at hc
  linear_combination -hc

theorem hessian_transport_hx_By
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hp : p ∈ U) :
    coordPartial 0 (fun q => covHessian g z q 1 1) p -
        coordPartial 1 (fun q => covHessian g z q 0 1) p =
      -christoffel g 0 1 1 p * covHessian g z p 0 0 +
        (christoffel g 0 0 1 p - christoffel g 1 1 1 p) * covHessian g z p 0 1 +
        christoffel g 1 0 1 p * covHessian g z p 1 1 +
        gaussianCurvature g p * (g p 0 1 * coordPartial 1 z p -
          g p 1 1 * coordPartial 0 z p) := by
  have hc := covHessian_commutator hg hU hz hp 0 1 1
  simp only [covDerivHessian, Fin.sum_univ_two, riemann_factorization hg hU hp] at hc
  simp [curvatureFactor] at hc
  simp only [covHessian_symm hg hU hz hp 1 0,
    christoffel_lower_symm hg hU hp 0 1 0,
    christoffel_lower_symm hg hU hp 1 1 0] at hc
  linear_combination hc

theorem darboux_determinant_derivative
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U)
    (hDarboux : ∀ q ∈ U, (covHessian g z q).det =
      gaussianCurvature g q * heightEnergy g z q)
    (hp : p ∈ U) (d : Fin 2) :
    coordPartial d (fun q => covHessian g z q 0 0) p * covHessian g z p 1 1 +
        covHessian g z p 0 0 * coordPartial d (fun q => covHessian g z q 1 1) p -
        2 * covHessian g z p 0 1 * coordPartial d (fun q => covHessian g z q 0 1) p =
      coordPartial d (gaussianCurvature g) p * heightEnergy g z p +
        gaussianCurvature g p * coordPartial d (heightEnergy g z) p := by
  have heq : (fun q => covHessian g z q 0 0 * covHessian g z q 1 1 -
      covHessian g z q 0 1 * covHessian g z q 0 1) =ᶠ[𝓝 p]
      (fun q => gaussianCurvature g q * heightEnergy g z q) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hq 1 0] using hDarboux q hq
  have hdH (i j : Fin 2) : DifferentiableAt ℝ (fun q => covHessian g z q i j) p :=
    (((covHessian_contDiffOn hg hU hz i j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdK : DifferentiableAt ℝ (gaussianCurvature g) p :=
    (((gaussianCurvature_contDiffOn hg hU) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdE : DifferentiableAt ℝ (heightEnergy g z) p :=
    (((heightEnergy_contDiffOn hg hU hz) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : coordPartial d
      (fun q => covHessian g z q 0 0 * covHessian g z q 1 1 -
        covHessian g z q 0 1 * covHessian g z q 0 1) p =
      coordPartial d (fun q => gaussianCurvature g q * heightEnergy g z q) p := by
    unfold coordPartial
    rw [heq.fderiv_eq]
  have hdprod : DifferentiableAt ℝ
      (fun q => covHessian g z q 0 0 * covHessian g z q 1 1) p :=
    (hdH 0 0).mul (hdH 1 1)
  have hdsq : DifferentiableAt ℝ
      (fun q => covHessian g z q 0 1 * covHessian g z q 0 1) p :=
    (hdH 0 1).mul (hdH 0 1)
  rw [HessianCalculus.coordPartial_sub_at hdprod hdsq d,
    HessianCalculus.coordPartial_mul_at (hdH 0 0) (hdH 1 1) d,
    HessianCalculus.coordPartial_mul_at (hdH 0 1) (hdH 0 1) d,
    HessianCalculus.coordPartial_mul_at hdK hdE d] at hd
  linear_combination hd

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_DarbouxJet
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

namespace DarbouxJetCalculus

theorem coordPartial_sq {f : Coord → ℝ} {u : Coord}
    (hf : DifferentiableAt ℝ f u) (i : Fin 2) :
    coordPartial i (fun v => (f v) ^ 2) u = 2 * f u * coordPartial i f u := by
  simp only [pow_two]
  rw [HessianCalculus.coordPartial_mul_at hf hf i]
  ring

end DarbouxJetCalculus

theorem coordPartial_jetConnection (g : MetricField) (p u : Coord) (a b i : Fin 2) :
    coordPartial i (jetConnection g p a b) u = christoffel g i a b p := by
  have h0 : DifferentiableAt ℝ (fun v : Coord => christoffel g 0 a b p * v 0) u :=
    (differentiableAt_apply (𝕜 := ℝ) 0 u).const_mul (christoffel g 0 a b p)
  have h1 : DifferentiableAt ℝ (fun v : Coord => christoffel g 1 a b p * v 1) u :=
    (differentiableAt_apply (𝕜 := ℝ) 1 u).const_mul (christoffel g 1 a b p)
  change coordPartial i (fun v => ∑ r, christoffel g r a b p * v r) u = _
  simp only [Fin.sum_univ_two]
  rw [HessianCalculus.coordPartial_add_at h0 h1 i,
    HessianCalculus.coordPartial_mul_at (differentiableAt_const (christoffel g 0 a b p))
      (differentiableAt_apply (𝕜 := ℝ) 0 u) i,
    HessianCalculus.coordPartial_mul_at (differentiableAt_const (christoffel g 1 a b p))
      (differentiableAt_apply (𝕜 := ℝ) 1 u) i]
  fin_cases i <;>
    simp [DarbouxJetCalculus.coordPartial_const, DarbouxJetCalculus.coordPartial_eval]

theorem coordPartial_jetMixed (g : MetricField) (p u : Coord) (b : ℝ) (i : Fin 2) :
    coordPartial i (jetMixed g p b) u = -christoffel g i 0 1 p := by
  change coordPartial i (fun v => b - jetConnection g p 0 1 v) u = _
  rw [HessianCalculus.coordPartial_sub_at (differentiableAt_const b)
    (jetConnection_differentiableAt g p u 0 1) i]
  simp [DarbouxJetCalculus.coordPartial_const, coordPartial_jetConnection]

theorem coordPartial_jetYY (g : MetricField) (p u : Coord) (c : ℝ) (i : Fin 2) :
    coordPartial i (jetYY g p c) u = -christoffel g i 1 1 p := by
  change coordPartial i (fun v => c - jetConnection g p 1 1 v) u = _
  rw [HessianCalculus.coordPartial_sub_at (differentiableAt_const c)
    (jetConnection_differentiableAt g p u 1 1) i]
  simp [DarbouxJetCalculus.coordPartial_const, coordPartial_jetConnection]

theorem coordPartial_jetNumerator (g : MetricField) (p u : Coord) (b : ℝ) (i : Fin 2) :
    coordPartial i (jetNumerator g p b) u =
      -2 * jetMixed g p b u * christoffel g i 0 1 p +
        gaussianCurvature g p * coordPartial i (jetEnergy g p) u := by
  have hsq : DifferentiableAt ℝ (fun v => (jetMixed g p b v) ^ 2) u := by
    simpa only [pow_two] using
      ((jetMixed_differentiableAt g p u b).hasFDerivAt.fun_mul
        (jetMixed_differentiableAt g p u b).hasFDerivAt).differentiableAt
  have hKE : DifferentiableAt ℝ
      (fun v => gaussianCurvature g p * jetEnergy g p v) u :=
    (jetEnergy_differentiableAt g p u).const_mul (gaussianCurvature g p)
  change coordPartial i (fun v => (jetMixed g p b v) ^ 2 +
    gaussianCurvature g p * jetEnergy g p v) u = _
  rw [HessianCalculus.coordPartial_add_at hsq hKE i,
    DarbouxJetCalculus.coordPartial_sq (jetMixed_differentiableAt g p u b) i,
    HessianCalculus.coordPartial_mul_at (differentiableAt_const (gaussianCurvature g p))
      (jetEnergy_differentiableAt g p u) i,
    coordPartial_jetMixed]
  simp only [DarbouxJetCalculus.coordPartial_const, zero_mul, zero_add]
  ring

theorem solvedDarboux_firstJet_expanded (g : MetricField) (p u : Coord) (b c : ℝ)
    (hne : jetYY g p c u ≠ 0) (i : Fin 2) :
    coordPartial i (solvedDarboux g p b c) u =
      christoffel g i 0 0 p - 2 * (jetMixed g p b u / jetYY g p c u) * christoffel g i 0 1 p +
        (jetMixed g p b u / jetYY g p c u) ^ 2 * christoffel g i 1 1 p +
        gaussianCurvature g p *
          (coordPartial i (jetEnergy g p) u / jetYY g p c u +
            jetEnergy g p u * christoffel g i 1 1 p / (jetYY g p c u) ^ 2) := by
  have hN := jetNumerator_differentiableAt g p u b
  have hH := jetYY_differentiableAt g p u c
  have hQ : DifferentiableAt ℝ
      (fun v => jetNumerator g p b v / jetYY g p c v) u := by
    simpa only [div_eq_mul_inv, Function.comp_def] using
      (hN.hasFDerivAt.fun_mul
        ((hasDerivAt_inv hne).comp_hasFDerivAt u hH.hasFDerivAt)).differentiableAt
  change coordPartial i (fun v => jetConnection g p 0 0 v +
    jetNumerator g p b v / jetYY g p c v) u = _
  rw [HessianCalculus.coordPartial_add_at (jetConnection_differentiableAt g p u 0 0) hQ i,
    coordPartial_jetConnection, coordPartial_div hN hH hne i,
    coordPartial_jetNumerator, coordPartial_jetYY]
  simp only [jetNumerator]
  field_simp [hne]
  ring

theorem christoffelAlongD_eq {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (q : ℝ) (i : Fin 2) :
    christoffelAlongD g p q i =
      christoffel g i 0 0 p - 2 * q * christoffel g i 0 1 p +
        q ^ 2 * christoffel g i 1 1 p := by
  simp only [christoffelAlongD, Fin.sum_univ_two, jetDriftVector,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [christoffel_lower_symm hg hU hp i 1 0]
  ring

theorem solvedDarboux_firstJet {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U)
    (u : Coord) (b c : ℝ) (hne : jetYY g p c u ≠ 0) (i : Fin 2) :
    coordPartial i (solvedDarboux g p b c) u =
      christoffelAlongD g p (jetMixed g p b u / jetYY g p c u) i +
        gaussianCurvature g p *
          (coordPartial i (jetEnergy g p) u / jetYY g p c u +
            jetEnergy g p u * christoffel g i 1 1 p / (jetYY g p c u) ^ 2) := by
  rw [christoffelAlongD_eq hg hU hp]
  exact solvedDarboux_firstJet_expanded g p u b c hne i

theorem jetEnergy_at_height {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) (z : Coord → ℝ) :
    jetEnergy g p (fun i => coordPartial i z p) = heightEnergy g z p := by
  symm
  exact heightEnergy_polynomial z hg hp

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_ActualDriftEquation
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem hessian_quotient_transport
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ q ∈ U, (covHessian g z q).det = gaussianCurvature g q * heightEnergy g z q)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p -
      hessianQuotient g z p * christoffelAlongD g p (hessianQuotient g z p) 0 -
      christoffelAlongD g p (hessianQuotient g z p) 1 =
        coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
        gaussianCurvature g p *
          (coordPartial 1 (heightEnergy g z) p / (covHessian g z p 1 1) ^ 2 -
            heightEnergy g z p * coordPartial 1 (fun q => covHessian g z q 1 1) p /
              (covHessian g z p 1 1) ^ 3 -
            darbouxG g z p * (christoffel g 0 0 1 p -
              hessianQuotient g z p * christoffel g 0 1 1 p) +
            driftJ g z p / covHessian g z p 1 1) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD p hp
  have hBx : coordPartial 0 (fun q => covHessian g z q 0 1) p -
      coordPartial 1 (fun q => covHessian g z q 0 0) p =
      -christoffel g 0 0 1 p * covHessian g z p 0 0 +
      (christoffel g 0 0 0 p - christoffel g 1 0 1 p) * covHessian g z p 0 1 +
      christoffel g 1 0 0 p * covHessian g z p 1 1 +
      gaussianCurvature g p * (g p 0 0 * coordPartial 1 z p - g p 0 1 * coordPartial 0 z p) := by
    linear_combination -hessian_transport_Ay_Bx hg hU hz hp
  have hs := SmoothLocal.DriftAlgebra.quotient_transport_algebra
    (covHessian g z p 0 0) (covHessian g z p 0 1) (covHessian g z p 1 1)
    (coordPartial 1 (fun q => covHessian g z q 0 0) p)
    (coordPartial 0 (fun q => covHessian g z q 0 1) p)
    (coordPartial 1 (fun q => covHessian g z q 0 1) p)
    (coordPartial 0 (fun q => covHessian g z q 1 1) p)
    (coordPartial 1 (fun q => covHessian g z q 1 1) p)
    (gaussianCurvature g p) (coordPartial 1 (gaussianCurvature g) p)
    (heightEnergy g z p) (coordPartial 1 (heightEnergy g z) p)
    (christoffel g 0 0 0 p) (christoffel g 0 0 1 p) (christoffel g 0 1 1 p)
    (christoffel g 1 0 0 p) (christoffel g 1 0 1 p) (christoffel g 1 1 1 p)
    (g p 0 0 * coordPartial 1 z p - g p 0 1 * coordPartial 0 z p)
    (g p 0 1 * coordPartial 1 z p - g p 1 1 * coordPartial 0 z p)
    hyy hdet (darboux_determinant_derivative hg hU hz hD hp 1) hBx
    (hessian_transport_hx_By hg hU hz hp)
  have hdH (i j : Fin 2) : DifferentiableAt ℝ (fun q => covHessian g z q i j) p :=
    (((covHessian_contDiffOn hg hU hz i j) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hqD := coordinateDrift_self_quotient (hdH 0 1) (hdH 1 1) hyy
  change coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p = _ at hqD
  rw [hqD, christoffelAlongD_eq hg hU hp, christoffelAlongD_eq hg hU hp]
  dsimp only [hessianQuotient, darbouxG, driftJ]
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem heightPFirst_eq
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    heightPFirst g z i p = christoffelAlongD g p (hessianQuotient g z p) i +
      gaussianCurvature g p *
        (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
          heightEnergy g z p * christoffel g i 1 1 p / (covHessian g z p 1 1) ^ 2) := by
  simpa only [heightPFirst, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z, hessianQuotient] using
    solvedDarboux_firstJet hg hU hp (fun r => coordPartial r z p)
      (coordPartial 0 (coordPartial 1 z) p) (coordPartial 1 (coordPartial 1 z) p) hyy i

theorem heightEnergy_jet_contraction (hg : SmoothPositiveOn g U) (hp : p ∈ U) :
    hessianQuotient g z p * coordPartial 0 (jetEnergy g p) (fun r => coordPartial r z p) +
      coordPartial 1 (jetEnergy g p) (fun r => coordPartial r z p) = -2 * driftJ g z p := by
  rw [coordPartial_jetEnergy, coordPartial_jetEnergy]
  norm_num
  rw [metric_coeff_symm hg hp 1 0]
  unfold driftJ
  ring

theorem geometric_quotient_drift
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ q ∈ U, (covHessian g z q).det = gaussianCurvature g q * heightEnergy g z q)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0) :
    coordinateDrift (hessianQuotient g z) (hessianQuotient g z) p -
      hessianQuotient g z p * heightPFirst g z 0 p - heightPFirst g z 1 p =
        coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
          gaussianCurvature g p * curvatureDriftError g z p := by
  have hd := hessian_quotient_transport hg hU hz hD hp hyy
  have he : coordPartial 1 (heightEnergy g z) p =
      2 * (christoffel g 0 0 1 p + christoffel g 1 1 1 p) * heightEnergy g z p -
        2 * covHessian g z p 1 1 * driftJ g z p :=
    heightEnergy_y_quotient hg hU hz hp hyy
  have hr := SmoothLocal.DriftAlgebra.explicit_drift_remainder
    (covHessian g z p 1 1) (heightEnergy g z p)
    (coordPartial 1 (fun q => covHessian g z q 1 1) p)
    (hessianQuotient g z p)
    (christoffel g 0 0 1 p) (christoffel g 0 1 1 p) (christoffel g 1 1 1 p)
    (driftJ g z p)
    (coordPartial 0 (jetEnergy g p) (fun r => coordPartial r z p))
    (coordPartial 1 (jetEnergy g p) (fun r => coordPartial r z p))
    (coordPartial 1 (heightEnergy g z) p) hyy he (heightEnergy_jet_contraction hg hp)
  rw [heightPFirst_eq hg hU hp hyy 0, heightPFirst_eq hg hU hp hyy 1,
    curvatureDriftError_eq]
  dsimp only [darbouxG, connectionTraceY] at hd ⊢
  linear_combination hd + gaussianCurvature g p * hr

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowExistence
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord}

theorem flowField_hasDerivAt_y (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U)
    {t y : ℝ} (hp : coordinatePoint t y ∈ U) :
    HasDerivAt (flowField q t) (-coordPartial 1 q (coordinatePoint t y)) y := by
  have hd := (hq.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact (hd.hasFDerivAt.comp_hasDerivAt y (coordinatePoint_hasDerivAt_y t y)).neg

theorem exists_flowField_lipschitz (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) :
    ∃ L : ℝ≥0, ∀ t ∈ Icc (-2 : ℝ) 2,
      LipschitzOnWith L (flowField q t) (closedBall (0 : ℝ) 3) := by
  have hc : ContinuousOn (coordPartial 1 q) modelSquare :=
    (partial_contDiffOn hq hU 1).continuousOn.mono hSU
  obtain ⟨M, hM⟩ := modelSquare_isCompact.exists_bound_of_continuousOn hc
  let L : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  refine ⟨L, ?_⟩
  intro t ht
  have hmem (y : ℝ) (hy : y ∈ closedBall (0 : ℝ) 3) :
      coordinatePoint t y ∈ modelSquare := by
    have hy' : |y| ≤ 3 := by simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hy
    exact coordinatePoint_mem_modelSquare ⟨by linarith [ht.1], by linarith [ht.2]⟩ (abs_le.mp hy')
  apply (convex_closedBall (0 : ℝ) 3).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun y hy => (flowField_hasDerivAt_y hq hU (hSU (hmem y hy))).hasDerivWithinAt)
  intro y hy
  change ‖-coordPartial 1 q (coordinatePoint t y)‖ ≤ max M 0
  rw [norm_neg]
  exact (hM _ (hmem y hy)).trans (le_max_left _ _)

theorem exists_cap_picard (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100) :
    ∃ L : ℝ≥0, IsPicardLindelof (flowField q)
      (⟨0, by norm_num⟩ : Icc (-2 : ℝ) 2) 0 3 2 (1 / 100) L := by
  obtain ⟨L, hL⟩ := exists_flowField_lipschitz hq hU hSU
  refine ⟨L, hL, ?_, ?_, ?_⟩
  · intro y hy
    have hy' : |y| ≤ 3 := by simpa only [mem_closedBall, Real.dist_eq, sub_zero,
      NNReal.coe_ofNat] using hy
    exact hq.continuousOn.neg.comp (by unfold coordinatePoint; fun_prop)
      (fun t ht => hSU (coordinatePoint_mem_modelSquare
        ⟨by linarith [ht.1], by linarith [ht.2]⟩ (abs_le.mp hy')))
  · intro t ht y hy
    have hy' : |y| ≤ 3 := by simpa only [mem_closedBall, Real.dist_eq, sub_zero,
      NNReal.coe_ofNat] using hy
    have hm := coordinatePoint_mem_modelSquare (t := t) (y := y)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ (abs_le.mp hy')
    simpa only [flowField, norm_neg, Real.norm_eq_abs, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat] using hsmall _ hm
  · norm_num

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapFlow
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric Filter Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem exists_cap_flow {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ContDiffOn ℝ ∞ (Y s) (Icc (-2 : ℝ) 2)) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        |Y s t - s| ≤ (1 : ℝ) / 100 * |t|) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, |Y s t - s| ≤ (1 : ℝ) / 50) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        |Y s t| ≤ (101 : ℝ) / 50 ∧ coordinatePoint t (Y s t) ∈ modelSquare) ∧
      (∃ J : ℝ≥0, ∀ t, LipschitzOnWith J (fun s => Y s t) (Icc (-2 : ℝ) 2)) := by
  obtain ⟨L, hPL⟩ := exists_cap_picard hq hU hSU hsmall
  obtain ⟨Y, hY, hconf, ⟨J, hJ⟩, hcont, htime⟩ :=
    exists_confined_continuous_picard_family hPL
  have hball (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) :
      s ∈ closedBall (0 : ℝ) (↑(2 : ℝ≥0)) := by
    simpa only [mem_closedBall, Real.dist_eq, sub_zero, NNReal.coe_ofNat] using abs_le.mpr hs
  have hz : (0 : ℝ) ∈ Icc (-2 : ℝ) 2 := by norm_num
  have hstart (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) : Y s 0 = s :=
    (hY s (hball s hs)).1
  have hderiv (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ)
      (ht : t ∈ Icc (-2 : ℝ) 2) :
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t :=
    (hY s (hball s hs)).2 t ht
  have hdispl (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ)
      (ht : t ∈ Icc (-2 : ℝ) 2) : |Y s t - s| ≤ (1 : ℝ) / 100 * |t| := by
    have hh := (htime s (hball s hs)).dist_le_mul t ht 0 hz
    rw [hstart s hs] at hh
    simpa only [Real.dist_eq, sub_zero, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh
  have hdispl' (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ)
      (ht : t ∈ Icc (-2 : ℝ) 2) : |Y s t - s| ≤ (1 : ℝ) / 50 := by
    have hd := hdispl s hs t ht
    have habs := abs_le.mpr ht
    nlinarith
  have hfield : ContDiffOn ℝ ∞ (uncurry (flowField q))
      (Icc (-2 : ℝ) 2 ×ˢ closedBall (0 : ℝ) 3) := by
    apply hq.neg.comp (by unfold coordinatePoint; fun_prop)
    intro p hp
    have hy : |p.2| ≤ 3 := by
      simpa only [mem_closedBall, Real.dist_eq, sub_zero] using hp.2
    exact hSU (coordinatePoint_mem_modelSquare
      ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩ (abs_le.mp hy))
  refine ⟨Y, hcont.mono (fun p hp => ⟨hball p.1 hp.1, hp.2⟩), ?_, hstart,
    hderiv, hdispl, hdispl', ?_, ⟨J, fun t => (hJ t).mono (fun s hs => hball s hs)⟩⟩
  · intro s hs
    exact ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt hfield (hderiv s hs)
      (fun t _ => hconf s (hball s hs) t)
  · intro s hs t ht
    have hys : |Y s t| ≤ (101 : ℝ) / 50 := by
      have hsum : |Y s t| ≤ |Y s t - s| + |s| := by
        simpa only [sub_add_cancel] using abs_add_le (Y s t - s) s
      have hd := hdispl' s hs t ht
      have hs2 := abs_le.mpr hs
      linarith
    refine ⟨hys, coordinatePoint_mem_modelSquare
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ ?_⟩
    exact abs_le.mp (hys.trans (by norm_num))

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Obstructions_PatchAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

theorem exists_open_hessianQuotient_domain
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hSU : modelSquare ⊆ U)
    (hyy : ∀ p ∈ modelSquare, covHessian g z p 1 1 ≠ 0) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      ContDiffOn ℝ ∞ (hessianQuotient g z) V := by
  let V := U ∩ (fun p => covHessian g z p 1 1) ⁻¹' ({0} : Set ℝ)ᶜ
  have hV : IsOpen V :=
    (covHessian_contDiffOn hg hU hz 1 1).continuousOn.isOpen_inter_preimage
      hU isClosed_singleton.isOpen_compl
  have hVU : V ⊆ U := fun _ hp => hp.1
  have hSV : modelSquare ⊆ V := fun p hp => ⟨hSU hp, hyy p hp⟩
  have hnonzero : ∀ p ∈ V, covHessian g z p 1 1 ≠ 0 := fun _ hp => hp.2
  have hgv : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  exact ⟨V, hV, hSV, hVU, hnonzero,
    hessianQuotient_contDiffOn hgv hV (hz.mono hVU) hnonzero⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_ClosedSquareJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow SmoothLocal.ODE

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem covHessian_coordinate_bound_closed_square
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|) (i j : Fin 2) :
    CoordinateBound (fun p => covHessian g z p i j) modelSquare 3 (hessianJetBound G Z d) := by
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun a b => (hg.1 a b).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hBI := covHessian_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ hd
    (fun a b => (hgB a b).restrict_domain interior_subset) (hzB.restrict_domain interior_subset)
    (fun p hp => hdet p (interior_subset hp)) i j
  exact CoordinateBound.of_modelSquare_interior (covHessian_contDiffOn hg hU hz i j) hU hSU hBI

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_ModelPrincipal
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Model
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem model_full_principal_lower
    {G K : Coord → ℝ} {p : Coord} {y kappa g0 rho rhoMax epsilon R MG Mq q : ℝ}
    (ell : ℕ) (hGdiff : DifferentiableAt ℝ G p) (hKdiff : DifferentiableAt ℝ K p)
    (hkappa : 0 < kappa) (hg0 : 0 < g0) (hG : g0 ≤ G p)
    (hrho : 0 < rho) (hrhoMax : rho ≤ rhoMax) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (ht : |p 0| ≤ R) (hq : |q| ≤ Mq)
    (hsmall : epsilon * R * Mq ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hy : y ≤ 1 / 50)
    (hGsi : |coordPartial 1 G p| ≤ MG) (hGti : |coordPartial 0 G p| ≤ MG)
    (hKvalue : K p = modelCurvature kappa ![p 0, y])
    (hKs : coordPartial 1 K p = coordPartial 1 (modelCurvature kappa) ![p 0, y] / rho)
    (hKt : coordPartial 0 K p = 2 * kappa * p 0 -
      q * coordPartial 1 (modelCurvature kappa) ![p 0, y])
    (hKsmall : |K p| ≤ modelPrincipalRadius g0 kappa rhoMax epsilon R MG ell) :
    modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 ≤
      directedPrincipal (fun z => G z * K z) ell epsilon p := by
  have hmax : 0 < rhoMax := hrho.trans_le hrhoMax
  have hR : 0 ≤ R := (abs_nonneg _).trans ht
  have hMG : 0 ≤ MG := (abs_nonneg _).trans hGsi
  have hmodel : |modelCurvature kappa ![p 0, y]| ≤ kappa / 8 := by
    rw [← hKvalue]
    exact hKsmall.trans (min_le_left _ _)
  have hgeo := model_geometric_principal_lower (p := ![p 0, y]) ell hkappa hg0 hG
    hrho hrhoMax heps (by simpa using ht) hq hsmall (by simpa using hy) hmodel
  simp only [Matrix.cons_val_zero] at hgeo
  have hcoeff := modelPrincipal_derivative_remainder_bound ell heps.le heps1 ht hGsi hGti
  have herr : |K p * (-((ell : ℝ) + 1 / 2) * coordPartial 1 G p +
      epsilon * p 0 * coordPartial 0 G p / 2)| ≤
      modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hcoeff (abs_nonneg _)).trans
      (modelPrincipal_radius_error ell hg0 hkappa hmax heps hR hMG hKsmall)
  have heq : directedPrincipal (fun z => G z * K z) ell epsilon p =
      G p * (-(((ell : ℝ) + 1 / 2) / rho + epsilon * p 0 * q / 2) *
        coordPartial 1 (modelCurvature kappa) ![p 0, y] + epsilon * kappa * (p 0) ^ 2) +
      K p * (-((ell : ℝ) + 1 / 2) * coordPartial 1 G p +
        epsilon * p 0 * coordPartial 0 G p / 2) := by
    unfold directedPrincipal
    rw [HessianCalculus.coordPartial_mul_at hGdiff hKdiff 1,
      HessianCalculus.coordPartial_mul_at hGdiff hKdiff 0, hKs, hKt]
    field_simp [hrho.ne']
    ring
  rw [heq]
  linarith [(abs_le.mp herr).1]

end SmoothLocal.Model

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowCurvature
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

variable {Y : ℝ → ℝ → ℝ}

theorem capFlowHeight_hasDerivAt_time {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) :
    HasDerivAt (Y (p 1)) (coordPartial 0 (capFlowHeight Y) p) (p 0) := by
  have hd : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd' : DifferentiableAt ℝ (capFlowHeight Y) (boxPoint (p 0) (p 1)) := by
    simpa only [boxPoint_coord_eta] using hd
  have hline := hd'.hasFDerivAt.comp_hasDerivAt (p 0) (boxPoint_hasDerivAt_t (p 0) (p 1))
  change HasDerivAt (fun t => capFlowHeight Y (boxPoint t (p 1)))
    (coordPartial 0 (capFlowHeight Y) (boxPoint (p 0) (p 1))) (p 0) at hline
  have hfun : (fun t => capFlowHeight Y (boxPoint t (p 1))) = Y (p 1) := by
    funext t
    simp [capFlowHeight, boxPoint]
  rw [hfun, boxPoint_coord_eta] at hline
  exact hline

theorem capFlowHeight_hasDerivAt_initial {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) :
    HasDerivAt (fun s => Y s (p 0)) (coordPartial 1 (capFlowHeight Y) p) (p 1) := by
  have hd : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd' : DifferentiableAt ℝ (capFlowHeight Y) (boxPoint (p 0) (p 1)) := by
    simpa only [boxPoint_coord_eta] using hd
  have hline := hd'.hasFDerivAt.comp_hasDerivAt (p 1) (boxPoint_hasDerivAt_s (p 0) (p 1))
  change HasDerivAt (fun s => capFlowHeight Y (boxPoint (p 0) s))
    (coordPartial 1 (capFlowHeight Y) (boxPoint (p 0) (p 1))) (p 1) at hline
  have hfun : (fun s => capFlowHeight Y (boxPoint (p 0) s)) = (fun s => Y s (p 0)) := by
    funext s
    simp [capFlowHeight, boxPoint]
  rw [hfun, boxPoint_coord_eta] at hline
  exact hline

variable {q : Coord → ℝ}

theorem capFlowHeight_partial_time {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hp : p ∈ capChartDomain) :
    coordPartial 0 (capFlowHeight Y) p = -q (capChart Y p) := by
  have ht : p 0 ∈ Ioo (-2 : ℝ) 2 := hp.1
  have hs : p 1 ∈ Ioo (-2 : ℝ) 2 := hp.2
  have ho := (hode (p 1) ⟨hs.1.le, hs.2.le⟩ (p 0) ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  exact (capFlowHeight_hasDerivAt_time hY hp).unique ho

theorem capFlowHeight_partial_initial_pos {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) : 0 < coordPartial 1 (capFlowHeight Y) p := by
  rw [← (capFlowHeight_hasDerivAt_initial hY hp).deriv]
  exact hvar (p 1) hp.2 (p 0) hp.1

theorem capChartRho_pos {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) : 0 < capChartRho Y p :=
  one_div_pos.mpr (capFlowHeight_partial_initial_pos hY hvar hp)

theorem capChartRho_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s) :
    ContDiffOn ℝ ∞ (capChartRho Y) capChartDomain :=
  contDiffOn_const.div (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1)
    (fun _ hp => (capFlowHeight_partial_initial_pos hY hvar hp).ne')

theorem capModelCurvature_partial (kappa : ℝ) {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (i : Fin 2) :
    coordPartial i (capModelCurvature kappa Y) p =
      (if i = 0 then 2 * kappa * p 0 else 0) +
        coordPartial 1 (modelCurvature kappa) (capChart Y p) * coordPartial i (capFlowHeight Y) p := by
  have hheight : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hh := ((modelProfile_contDiff.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (capFlowHeight Y p)).hasDerivAt).comp_hasFDerivAt
    p hheight.hasFDerivAt
  have hx := hasFDerivAt_apply (𝕜 := ℝ) 0 p
  have hd := ((hx.pow 2).sub hh).const_mul kappa
  simp only [Function.comp_def, Pi.sub_def] at hd
  have hfun : capModelCurvature kappa Y =
      (fun z => kappa * ((z 0) ^ 2 - modelProfile (capFlowHeight Y z))) := by
    funext z
    simp only [capModelCurvature, modelCurvature, capChart_zero, capChart_one]
  rw [hfun, modelCurvature_partial]
  simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, capChart_one, coordPartial]
  rw [hd.fderiv]
  fin_cases i <;> simp <;> ring

theorem capModelCurvature_partial_time (kappa : ℝ) {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hp : p ∈ capChartDomain) :
    coordPartial 0 (capModelCurvature kappa Y) p = 2 * kappa * p 0 -
      q (capChart Y p) * coordPartial 1 (modelCurvature kappa) (capChart Y p) := by
  rw [capModelCurvature_partial kappa hY hp 0, capFlowHeight_partial_time hY hode hp]
  norm_num only [↓reduceIte, if_true]
  ring

theorem capModelCurvature_partial_initial (kappa : ℝ) {p : Coord}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) :
    coordPartial 1 (capModelCurvature kappa Y) p =
      coordPartial 1 (modelCurvature kappa) (capChart Y p) / capChartRho Y p := by
  rw [capModelCurvature_partial kappa hY hp 1]
  simp [capChartRho, div_eq_mul_inv]

theorem cap_model_full_principal_lower
    {G : Coord → ℝ} {p : Coord} {kappa g0 rhoMax epsilon MG : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hdisp : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      |Y s t - s| ≤ (1 : ℝ) / 50)
    (hqsmall : ∀ z ∈ modelSquare, |q z| ≤ (1 : ℝ) / 100)
    (hp : p ∈ capChartDomain) (hs : p 1 ≤ 0) (ell : ℕ)
    (hGdiff : DifferentiableAt ℝ G p) (hkappa : 0 < kappa) (hg0 : 0 < g0)
    (hG : g0 ≤ G p) (hrhoMax : capChartRho Y p ≤ rhoMax)
    (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hsmall : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hGsi : |coordPartial 1 G p| ≤ MG) (hGti : |coordPartial 0 G p| ≤ MG)
    (hKsmall : |capModelCurvature kappa Y p| ≤
      modelPrincipalRadius g0 kappa rhoMax epsilon 2 MG ell) :
    modelCoercivityMargin g0 kappa rhoMax epsilon ell / 2 ≤
      directedPrincipal (fun z => G z * capModelCurvature kappa Y z) ell epsilon p := by
  have hdispP : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50 :=
    hdisp (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩
  have hy : capFlowHeight Y p ≤ 1 / 50 := by linarith [(abs_le.mp hdispP).2]
  have hKdiff : DifferentiableAt ℝ (capModelCurvature kappa Y) p :=
    ((capModelCurvature_contDiffOn kappa hY).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hKvalue : capModelCurvature kappa Y p =
      modelCurvature kappa ![p 0, capFlowHeight Y p] := by
    unfold capModelCurvature
    rw [capChart_eq_vec]
  have hKs : coordPartial 1 (capModelCurvature kappa Y) p =
      coordPartial 1 (modelCurvature kappa) ![p 0, capFlowHeight Y p] / capChartRho Y p := by
    rw [capModelCurvature_partial_initial kappa hY hp, capChart_eq_vec]
  have hKt : coordPartial 0 (capModelCurvature kappa Y) p =
      2 * kappa * p 0 - q (capChart Y p) *
        coordPartial 1 (modelCurvature kappa) ![p 0, capFlowHeight Y p] := by
    rw [capModelCurvature_partial_time kappa hY hode hp]
    rw [capChart_eq_vec]
  exact model_full_principal_lower ell hGdiff hKdiff hkappa hg0 hG
    (capChartRho_pos hY hvar hp) hrhoMax heps heps1 (abs_lt.mpr hp.1).le
    (hqsmall _ (capChart_mem_modelSquare hp hdispP)) hsmall hy hGsi hGti hKvalue hKs hKt hKsmall

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowTransport
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def capTransportA (Y : ℝ → ℝ → ℝ) (a : Coord → ℝ) (p : Coord) : ℝ :=
  capPullback Y a p * (capChartRho Y p) ^ 2

def capTransportC (Y : ℝ → ℝ → ℝ) (a C0 : Coord → ℝ) (p : Coord) : ℝ :=
  capPullback Y a p * capChartSigma Y p + capPullback Y C0 p * capChartRho Y p

variable {Y : ℝ → ℝ → ℝ} {u q : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem capChart_partial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (i : Fin 2) :
    coordPartial i (capChart Y) p =
      (if i = 0 then Pi.single 0 (1 : ℝ) else 0) +
        coordPartial i (capFlowHeight Y) p • Pi.single 1 (1 : ℝ) := by
  have hheight : DifferentiableAt ℝ (capFlowHeight Y) p :=
    ((capFlowHeight_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : HasFDerivAt (fun z : Coord => z 0 • (Pi.single 0 (1 : ℝ) : Coord) +
      capFlowHeight Y z • (Pi.single 1 (1 : ℝ) : Coord))
      ((ContinuousLinearMap.proj 0).smulRight (Pi.single 0 (1 : ℝ) : Coord) +
        (fderiv ℝ (capFlowHeight Y) p).smulRight (Pi.single 1 (1 : ℝ) : Coord)) p :=
    ((hasFDerivAt_apply (𝕜 := ℝ) 0 p).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add
      (hheight.hasFDerivAt.smul_const (Pi.single 1 (1 : ℝ) : Coord))
  change fderiv ℝ (fun z : Coord => z 0 • (Pi.single 0 (1 : ℝ) : Coord) +
    capFlowHeight Y z • (Pi.single 1 (1 : ℝ) : Coord)) p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp [coordPartial]

theorem capPullback_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hmap : MapsTo (capChart Y) capChartDomain U) :
    ContDiffOn ℝ ∞ (capPullback Y u) capChartDomain :=
  hu.comp (capChart_contDiffOn hY) hmap

theorem capPullback_partial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) (i : Fin 2) :
    coordPartial i (capPullback Y u) p =
      (if i = 0 then coordPartial 0 u (capChart Y p) else 0) +
        coordPartial 1 u (capChart Y p) * coordPartial i (capFlowHeight Y) p := by
  have hchart : DifferentiableAt ℝ (capChart Y) p :=
    ((capChart_contDiffOn hY).contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change fderiv ℝ (u ∘ capChart Y) p (Pi.single i 1) = _
  rw [fderiv_comp p hu hchart, ContinuousLinearMap.comp_apply]
  change fderiv ℝ u (capChart Y p) (coordPartial i (capChart Y) p) = _
  rw [capChart_partial hY hp i]
  fin_cases i <;> simp [coordPartial, smul_eq_mul] <;> ring

theorem capPullback_partial_initial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) :
    coordPartial 1 (capPullback Y u) p =
      capPullback Y (coordPartial 1 u) p * coordPartial 1 (capFlowHeight Y) p := by
  simpa only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte, zero_add, capPullback] using
    capPullback_partial hY hp hu 1

theorem capPullback_partial_time
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) :
    coordPartial 0 (capPullback Y u) p = coordinateDrift q u (capChart Y p) := by
  rw [capPullback_partial hY hp hu 0, capFlowHeight_partial_time hY hode hp]
  simp only [↓reduceIte, coordinateDrift]
  ring

theorem capPullback_original_y
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) (hu : DifferentiableAt ℝ u (capChart Y p)) :
    capPullback Y (coordPartial 1 u) p = capChartRho Y p * coordPartial 1 (capPullback Y u) p := by
  rw [capPullback_partial_initial hY hp hu, capChartRho]
  field_simp [(capFlowHeight_partial_initial_pos hY hvar hp).ne']

theorem capPullback_second_initial_forward
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    coordPartial 1 (coordPartial 1 (capPullback Y u)) p =
      capPullback Y (coordPartial 1 (coordPartial 1 u)) p *
          (coordPartial 1 (capFlowHeight Y) p) ^ 2 +
        capPullback Y (coordPartial 1 u) p * coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p := by
  have huy := partial_contDiffOn hu hU 1
  have hPuy := capPullback_contDiffOn hY huy hmap
  have hYs := partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1
  have he : coordPartial 1 (capPullback Y u) =ᶠ[𝓝 p]
      (fun z => capPullback Y (coordPartial 1 u) z * coordPartial 1 (capFlowHeight Y) z) := by
    filter_upwards [capChartDomain_isOpen.mem_nhds hp] with z hz
    exact capPullback_partial_initial hY hz
      ((hu.contDiffAt (hU.mem_nhds (hmap hz))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hd := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single 1 (1 : ℝ))) he.fderiv_eq
  change coordPartial 1 (coordPartial 1 (capPullback Y u)) p =
    coordPartial 1 (fun z => capPullback Y (coordPartial 1 u) z * coordPartial 1 (capFlowHeight Y) z) p at hd
  rw [hd, HessianCalculus.coordPartial_mul_at
    ((hPuy.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hYs.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) 1,
    capPullback_partial_initial hY hp
      ((huy.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  ring

theorem capPullback_original_yy
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    capPullback Y (coordPartial 1 (coordPartial 1 u)) p =
      (capChartRho Y p) ^ 2 * coordPartial 1 (coordPartial 1 (capPullback Y u)) p +
        capChartSigma Y p * coordPartial 1 (capPullback Y u) p := by
  rw [capPullback_second_initial_forward hY hu hU hmap hp,
    capPullback_partial_initial hY hp
      ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  unfold capChartRho capChartSigma
  field_simp [(capFlowHeight_partial_initial_pos hY hvar hp).ne']
  ring

theorem capPullback_drift_twice
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    capPullback Y (coordinateDrift q (coordinateDrift q u)) p =
      coordPartial 0 (coordPartial 0 (capPullback Y u)) p := by
  have hDu := coordinateDrift_contDiffOn hq hu hU
  have he : coordPartial 0 (capPullback Y u) =ᶠ[𝓝 p] capPullback Y (coordinateDrift q u) := by
    filter_upwards [capChartDomain_isOpen.mem_nhds hp] with z hz
    exact capPullback_partial_time hY hode hz
      ((hu.contDiffAt (hU.mem_nhds (hmap hz))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hd := congrArg (fun L : Coord →L[ℝ] ℝ => L (Pi.single 0 (1 : ℝ))) he.fderiv_eq
  change coordPartial 0 (coordPartial 0 (capPullback Y u)) p =
    coordPartial 0 (capPullback Y (coordinateDrift q u)) p at hd
  rw [hd, capPullback_partial_time hY hode hp
    ((hDu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  rfl

theorem capChartRho_partial_initial
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hp : p ∈ capChartDomain) :
    coordPartial 1 (capChartRho Y) p =
      -coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p /
        (coordPartial 1 (capFlowHeight Y) p) ^ 2 := by
  have hYs := partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1
  change coordPartial 1 (fun z => (1 : ℝ) / coordPartial 1 (capFlowHeight Y) z) p = _
  rw [coordPartial_div (differentiableAt_const (1 : ℝ))
    ((hYs.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (capFlowHeight_partial_initial_pos hY hvar hp).ne' 1]
  simp [coordPartial]

theorem capChartSigma_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s) :
    ContDiffOn ℝ ∞ (capChartSigma Y) capChartDomain := by
  have hYs := partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1
  exact (partial_contDiffOn hYs capChartDomain_isOpen 1).neg.div (hYs.pow 3)
    (fun p hp => pow_ne_zero 3 (capFlowHeight_partial_initial_pos hY hvar hp).ne')

theorem capTransportA_partial_initial {a : Coord → ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    coordPartial 1 (capTransportA Y a) p =
      capChartRho Y p * capPullback Y (coordPartial 1 a) p +
        2 * capPullback Y a p * capChartSigma Y p := by
  have hPa : DifferentiableAt ℝ (capPullback Y a) p :=
    ((capPullback_contDiffOn hY ha hmap).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hrho : DifferentiableAt ℝ (capChartRho Y) p :=
    ((capChartRho_contDiffOn hY hvar).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  unfold capTransportA
  simp only [pow_two]
  have hrhorho : DifferentiableAt ℝ (fun z => capChartRho Y z * capChartRho Y z) p :=
    hrho.mul hrho
  rw [HessianCalculus.coordPartial_mul_at hPa hrhorho 1,
    HessianCalculus.coordPartial_mul_at hrho hrho 1,
    capPullback_partial_initial hY hp
      ((ha.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    capChartRho_partial_initial hY hvar hp]
  unfold capChartRho capChartSigma
  field_simp [(capFlowHeight_partial_initial_pos hY hvar hp).ne']
  ring

theorem cap_driftOperator_transport (a B C0 : Coord → ℝ)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    capPullback Y (driftOperator q a B C0 u) p =
      multiplierOperator (capTransportA Y a) (capPullback Y B)
        (capTransportC Y a C0) (capPullback Y u) p := by
  have hud := ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  change capPullback Y (coordinateDrift q (coordinateDrift q u)) p +
    a (capChart Y p) * capPullback Y (coordPartial 1 (coordPartial 1 u)) p +
    B (capChart Y p) * coordinateDrift q u (capChart Y p) +
    C0 (capChart Y p) * capPullback Y (coordPartial 1 u) p = _
  rw [capPullback_drift_twice hY hode hq hu hU hmap hp,
    capPullback_original_yy hY hvar hu hU hmap hp,
    ← capPullback_partial_time hY hode hp hud,
    capPullback_original_y hY hvar hp hud]
  unfold multiplierOperator capTransportA capTransportC capPullback
  ring

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapJacobian
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capChart_fderiv_matrix {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    {p : Coord} (hp : p ∈ capChartDomain) :
    LinearMap.toMatrix' (fderiv ℝ (capChart Y) p).toLinearMap =
      !![1,0; coordPartial 0 (capFlowHeight Y) p,coordPartial 1 (capFlowHeight Y) p] := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  change coordPartial j (capChart Y) p i = _
  rw [capChart_partial hYs hp j]
  fin_cases i <;> fin_cases j <;> simp

theorem capChart_det_fderiv {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    {p : Coord} (hp : p ∈ capChartDomain) :
    (fderiv ℝ (capChart Y) p).det = coordPartial 1 (capFlowHeight Y) p := by
  rw [ContinuousLinearMap.det,←LinearMap.det_toMatrix',capChart_fderiv_matrix hYs hp]
  simp [Matrix.det_fin_two]

theorem capChart_abs_det_fderiv {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |(fderiv ℝ (capChart Y) p).det| = coordPartial 1 (capFlowHeight Y) p := by
  rw [capChart_det_fderiv hYs hp,abs_of_pos (capFlowHeight_partial_initial_pos hYs hvar hp)]

theorem capChart_jacobian_bounds
    {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) :
    Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
      coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M) := by
  have hYs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  rw [←(capFlowHeight_hasDerivAt_initial hYs hp).deriv]
  exact cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hMq hp.2 hp.1

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticEnergy
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem ellipticFluxT_partial_t
    (hv : DifferentiableAt ℝ v p) (hu : DifferentiableAt ℝ u p)
    (hut : DifferentiableAt ℝ (coordPartial 0 u) p) :
    coordPartial 0 (ellipticFluxT v u) p =
      -(coordPartial 0 v p * u p * coordPartial 0 u p +
        v p * (coordPartial 0 u p) ^ 2 +
        v p * u p * coordPartial 0 (coordPartial 0 u) p) := by
  have hd := ((hv.hasFDerivAt.fun_mul hu.hasFDerivAt).fun_mul hut.hasFDerivAt).neg
  change HasFDerivAt (fun x => -(v x * u x * coordPartial 0 u x)) _ p at hd
  simp only [coordPartial] at hd
  change coordPartial 0 (fun q => -(v q * u q * coordPartial 0 u q)) p = _
  simp only [coordPartial]
  rw [hd.fderiv]
  simp only [neg_apply, add_apply, smul_apply, smul_eq_mul]
  ring

theorem ellipticFluxS_partial_s
    (hA : DifferentiableAt ℝ A p) (hv : DifferentiableAt ℝ v p)
    (hu : DifferentiableAt ℝ u p) (hus : DifferentiableAt ℝ (coordPartial 1 u) p) :
    coordPartial 1 (ellipticFluxS A v u) p =
      -(coordPartial 1 (fun q => A q * v q) p * u p * coordPartial 1 u p +
        A p * v p * (coordPartial 1 u p) ^ 2 +
        A p * v p * u p * coordPartial 1 (coordPartial 1 u) p) := by
  have hAv : DifferentiableAt ℝ (fun q => A q * v q) p := hA.mul hv
  have hd := ((hAv.hasFDerivAt.fun_mul hu.hasFDerivAt).fun_mul hus.hasFDerivAt).neg
  change HasFDerivAt (fun x => -(A x * v x * u x * coordPartial 1 u x)) _ p at hd
  simp only [coordPartial] at hd
  change coordPartial 1 (fun q => -(A q * v q * u q * coordPartial 1 u q)) p = _
  simp only [coordPartial]
  rw [hd.fderiv]
  simp only [neg_apply, add_apply, smul_apply, smul_eq_mul]
  ring

theorem elliptic_divergence_identity
    (hA : DifferentiableAt ℝ A p) (hv : DifferentiableAt ℝ v p)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U) (hp : p ∈ U) :
    multiplierOperator A B C u p * (-v p * u p) =
      coordPartial 0 (ellipticFluxT v u) p + coordPartial 1 (ellipticFluxS A v u) p +
        ellipticEnergy A v u p + ellipticError A B C v u p := by
  have hud : DifferentiableAt ℝ u p :=
    (hu.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdu (i : Fin 2) : DifferentiableAt ℝ (coordPartial i u) p :=
    ((partial_contDiffOn hu hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [ellipticFluxT_partial_t hv hud (hdu 0), ellipticFluxS_partial_s hA hv hud (hdu 1)]
  unfold multiplierOperator ellipticEnergy ellipticError ellipticErrorT ellipticErrorS
  ring

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticAbsorption
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem ellipticErrors_zero_of_nonneg
    (hU : IsOpen U) (hp : p ∈ U) (hA : DifferentiableAt ℝ A p)
    (hv : DifferentiableAt ℝ v p) (hvn : ∀ q ∈ U, 0 ≤ v q) (hzero : v p = 0) :
    ellipticErrorT B v p = 0 ∧ ellipticErrorS A C v p = 0 := by
  have hmin : IsLocalMin v p := by
    change ∀ᶠ q in 𝓝 p, v p ≤ v q
    filter_upwards [hU.mem_nhds hp] with q hq
    simpa only [hzero] using hvn q hq
  have hdv := hmin.fderiv_eq_zero
  have hpv (i : Fin 2) : coordPartial i v p = 0 := by simp [coordPartial, hdv]
  constructor
  · simp [ellipticErrorT, hpv 0, hzero]
  · rw [ellipticErrorS, HessianCalculus.coordPartial_mul_at hA hv 1]
    simp [hpv 1, hzero]

theorem ellipticError_abs_bound
    (hU : IsOpen U) (hp : p ∈ U) (hA : DifferentiableAt ℝ A p)
    (hv : DifferentiableAt ℝ v p) (hvn : ∀ q ∈ U, 0 ≤ v q)
    (H : ℝ) (hH : 0 ≤ H)
    (hpos : 0 < v p → 0 < A p)
    (hratio : 0 < v p → (ellipticErrorT B v p) ^ 2 / v p +
      (ellipticErrorS A C v p) ^ 2 / (A p * v p) ≤ H) :
    |ellipticError A B C v u p| ≤ ellipticEnergy A v u p / 2 + H * (u p) ^ 2 / 2 := by
  by_cases hzero : v p = 0
  · have hz := ellipticErrors_zero_of_nonneg (B := B) (C := C) hU hp hA hv hvn hzero
    simp only [ellipticError, ellipticEnergy, hz.1, hz.2, hzero,
      zero_mul, add_zero, mul_zero, abs_zero, zero_div, zero_add]
    exact div_nonneg (mul_nonneg hH (sq_nonneg _)) (by norm_num)
  · have hvpos : 0 < v p := lt_of_le_of_ne (hvn p hp) (Ne.symm hzero)
    exact elliptic_error_scalar_bound (A p) (v p) (u p)
      (coordPartial 0 u p) (coordPartial 1 u p)
      (ellipticErrorT B v p) (ellipticErrorS A C v p) H hvpos (hpos hvpos) (hratio hvpos)

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticC1
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

variable {U : Set Coord} {f : Coord → ℝ}

variable {tl tr sb st : ℝ}

theorem rectangleIntegral_partial_t_zero_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ s ∈ Icc sb st, f (boxPoint tl s) = 0 ∧ f (boxPoint tr s) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 0 f) = 0 := by
  have hinner (s : ℝ) (hs' : s ∈ Icc sb st) :
      (∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun t => coordPartial 0 f (boxPoint t s)) (uIcc tl tr) := by
      rw [uIcc_of_le ht]
      exact (coordPartial_continuousOn_one hf hU 0).comp
        (by unfold boxPoint; fun_prop) (fun t ht' => hbox (boxPoint_mem ht' hs'))
    have hderiv (t : ℝ) (ht' : t ∈ uIcc tl tr) :
        HasDerivAt (fun x => f (boxPoint x s)) (coordPartial 0 f (boxPoint t s)) t := by
      have hp : boxPoint t s ∈ U := hbox (boxPoint_mem
        (by simpa only [uIcc_of_le ht] using ht') hs')
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      exact hd.hasFDerivAt.comp_hasDerivAt t (boxPoint_hasDerivAt_t t s)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [(hedge s hs').1, (hedge s hs').2, sub_self] at he
    exact he
  unfold rectangleIntegral
  calc
    (∫ s in sb..st, ∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) =
        ∫ _ in sb..st, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro s hs'
      exact hinner s (by simpa only [uIcc_of_le hs] using hs')
    _ = 0 := intervalIntegral.integral_zero

theorem rectangleIntegral_partial_s_zero_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ t ∈ Icc tl tr, f (boxPoint t sb) = 0 ∧ f (boxPoint t st) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 1 f) = 0 := by
  rw [rectangleIntegral_swap ht hs ((coordPartial_continuousOn_one hf hU 1).mono hbox)]
  have hinner (t : ℝ) (ht' : t ∈ Icc tl tr) :
      (∫ s in sb..st, coordPartial 1 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun s => coordPartial 1 f (boxPoint t s)) (uIcc sb st) := by
      rw [uIcc_of_le hs]
      exact (coordPartial_continuousOn_one hf hU 1).comp
        (by unfold boxPoint; fun_prop) (fun s hs' => hbox (boxPoint_mem ht' hs'))
    have hderiv (s : ℝ) (hs' : s ∈ uIcc sb st) :
        HasDerivAt (fun y => f (boxPoint t y)) (coordPartial 1 f (boxPoint t s)) s := by
      have hp : boxPoint t s ∈ U := hbox (boxPoint_mem ht'
        (by simpa only [uIcc_of_le hs] using hs'))
      have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      exact hd.hasFDerivAt.comp_hasDerivAt s (boxPoint_hasDerivAt_s t s)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
    rw [(hedge t ht').1, (hedge t ht').2, sub_self] at he
    exact he
  calc
    (∫ t in tl..tr, ∫ s in sb..st, coordPartial 1 f (boxPoint t s)) =
        ∫ _ in tl..tr, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht'
      exact hinner t (by simpa only [uIcc_of_le ht] using ht')
    _ = 0 := intervalIntegral.integral_zero

variable {A B C v u : Coord → ℝ}

theorem integrated_elliptic_identity_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v) :
    rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p * (-v p * u p)) =
      rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
  obtain ⟨hFt, hFs, hE, hErr⟩ := elliptic_fields_C1 hU hA hB hC hv hu
  have htzero : rectangleIntegral tl tr sb st (coordPartial 0 (ellipticFluxT v u)) = 0 := by
    apply rectangleIntegral_partial_t_zero_C1 ht hs hU hFt hbox
    intro s hs'
    constructor <;> simp [ellipticFluxT, (hboundary.1 s hs').1, (hboundary.1 s hs').2]
  have hszero : rectangleIntegral tl tr sb st (coordPartial 1 (ellipticFluxS A v u)) = 0 := by
    apply rectangleIntegral_partial_s_zero_C1 ht hs hU hFs hbox
    intro t ht'
    constructor <;> simp [ellipticFluxS, (hboundary.2 t ht').1, (hboundary.2 t ht').2]
  have hdt := (coordPartial_continuousOn_one hFt hU 0).mono hbox
  have hds := (coordPartial_continuousOn_one hFs hU 1).mono hbox
  calc
    rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p * (-v p * u p)) =
        rectangleIntegral tl tr sb st (fun p => coordPartial 0 (ellipticFluxT v u) p +
          coordPartial 1 (ellipticFluxS A v u) p + ellipticEnergy A v u p +
          ellipticError A B C v u p) := by
      apply rectangleIntegral_congr ht hs
      intro p hp
      exact elliptic_divergence_identity (B := B) (C := C)
        ((hA.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        ((hv.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hu hU (hbox hp)
    _ = rectangleIntegral tl tr sb st (coordPartial 0 (ellipticFluxT v u)) +
        rectangleIntegral tl tr sb st (coordPartial 1 (ellipticFluxS A v u)) +
        rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
      have hsum : ContinuousOn (fun p => coordPartial 0 (ellipticFluxT v u) p +
          coordPartial 1 (ellipticFluxS A v u) p) (closedRectangle tl tr sb st) :=
        hdt.add hds
      have hsumE : ContinuousOn (fun p => coordPartial 0 (ellipticFluxT v u) p +
          coordPartial 1 (ellipticFluxS A v u) p + ellipticEnergy A v u p)
          (closedRectangle tl tr sb st) := hsum.add (hE.mono hbox)
      rw [rectangleIntegral_add ht hs hsumE (hErr.mono hbox),
        rectangleIntegral_add ht hs hsum (hE.mono hbox),
        rectangleIntegral_add ht hs hdt hds]
    _ = rectangleIntegral tl tr sb st (ellipticEnergy A v u) +
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
      rw [htzero, hszero]
      ring

theorem integrated_elliptic_equation_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p) :
    rectangleIntegral tl tr sb st (ellipticEnergy A v u) =
      -rectangleIntegral tl tr sb st (fun p => v p * u p * f p) -
        rectangleIntegral tl tr sb st (ellipticError A B C v u) := by
  have hid := integrated_elliptic_identity_C1 ht hs hU hA hB hC hv hu hbox hboundary
  have hsource : rectangleIntegral tl tr sb st
      (fun p => multiplierOperator A B C u p * (-v p * u p)) =
      -rectangleIntegral tl tr sb st (fun p => v p * u p * f p) := by
    calc
      rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p * (-v p * u p)) =
          rectangleIntegral tl tr sb st (fun p => -(v p * u p * f p)) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        dsimp only
        rw [hEq p (hbox hp)]
        ring
      _ = -rectangleIntegral tl tr sb st (fun p => v p * u p * f p) :=
        rectangleIntegral_neg tl tr sb st _
  linarith

theorem integrated_elliptic_energy_bound_C1
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U) (hboundary : zeroRectangleBoundary tl tr sb st v)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p)
    (V H : ℝ) (hV : 0 ≤ V) (hH : 0 ≤ H)
    (hvn : ∀ p ∈ U, 0 ≤ v p)
    (hvV : ∀ p ∈ closedRectangle tl tr sb st, v p ≤ V)
    (hpos : ∀ p ∈ closedRectangle tl tr sb st, 0 < v p → 0 < A p)
    (hratio : ∀ p ∈ closedRectangle tl tr sb st, 0 < v p →
      (ellipticErrorT B v p) ^ 2 / v p + (ellipticErrorS A C v p) ^ 2 / (A p * v p) ≤ H) :
    rectangleIntegral tl tr sb st (ellipticEnergy A v u) ≤
      V * rectangleIntegral tl tr sb st (fun p => (f p) ^ 2) +
        (V + H) * rectangleIntegral tl tr sb st (fun p => (u p) ^ 2) := by
  have hf : ContDiffOn ℝ ∞ f U :=
    (ellipticOperator_contDiffOn hU hA hB hC hu).congr (fun p hp => (hEq p hp).symm)
  obtain ⟨_, _, hE, hErr⟩ := elliptic_fields_C1 hU hA hB hC hv hu
  have hSource : ContinuousOn (fun p => v p * u p * f p) U :=
    (hv.continuousOn.mul hu.continuousOn).mul hf.continuousOn
  have hpoint (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :
      -(v p * u p * f p) - ellipticError A B C v u p ≤
        (1 / 2 : ℝ) * ellipticEnergy A v u p +
          ((V + H) / 2) * (u p) ^ 2 + (V / 2) * (f p) ^ 2 := by
    have hpU := hbox hp
    have hErrBound := ellipticError_abs_bound (u := u) hU hpU
      ((hA.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      ((hv.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      hvn H hH (hpos p hp) (hratio p hp)
    have hyoung : -(u p * f p) ≤ ((u p) ^ 2 + (f p) ^ 2) / 2 := by
      nlinarith [sq_nonneg (u p + f p)]
    have hm := mul_le_mul_of_nonneg_left hyoung (hvn p hpU)
    have hcost := mul_le_mul (hvV p hp)
      (le_refl (((u p) ^ 2 + (f p) ^ 2) / 2))
      (div_nonneg (add_nonneg (sq_nonneg (u p)) (sq_nonneg (f p)))
        (by norm_num : (0 : ℝ) ≤ 2)) hV
    have hsource : -(v p * u p * f p) ≤ V * ((u p) ^ 2 + (f p) ^ 2) / 2 := by
      nlinarith [hm, hcost]
    nlinarith [hsource, neg_le_abs (ellipticError A B C v u p)]
  have hEhalf : ContinuousOn (fun p => (1 / 2 : ℝ) * ellipticEnergy A v u p)
      (closedRectangle tl tr sb st) := (continuousOn_const.mul hE).mono hbox
  have hUhalf : ContinuousOn (fun p => ((V + H) / 2) * (u p) ^ 2)
      (closedRectangle tl tr sb st) := (continuousOn_const.mul (hu.continuousOn.pow 2)).mono hbox
  have hFhalf : ContinuousOn (fun p => (V / 2) * (f p) ^ 2)
      (closedRectangle tl tr sb st) := (continuousOn_const.mul (hf.continuousOn.pow 2)).mono hbox
  have hNegSource : ContinuousOn (fun p => -(v p * u p * f p)) U := hSource.neg
  have hi := rectangleIntegral_mono ht hs
    ((hNegSource.sub hErr).mono hbox) ((hEhalf.add hUhalf).add hFhalf) hpoint
  simp only [Pi.add_def, Pi.sub_def] at hi
  have hsum : ContinuousOn (fun p => (1 / 2 : ℝ) * ellipticEnergy A v u p +
      ((V + H) / 2) * (u p) ^ 2) (closedRectangle tl tr sb st) := hEhalf.add hUhalf
  have heq := integrated_elliptic_equation_C1 ht hs hU hA hB hC hv hu hbox hboundary hEq
  have hleft : rectangleIntegral tl tr sb st
      (fun p => -(v p * u p * f p) - ellipticError A B C v u p) =
      rectangleIntegral tl tr sb st (ellipticEnergy A v u) := by
    rw [rectangleIntegral_sub ht hs (hNegSource.mono hbox) (hErr.mono hbox), rectangleIntegral_neg]
    exact heq.symm
  rw [hleft,
    rectangleIntegral_add ht hs hsum hFhalf,
    rectangleIntegral_add ht hs hEhalf hUhalf,
    rectangleIntegral_const_mul tl tr sb st (1 / 2 : ℝ) (ellipticEnergy A v u),
    rectangleIntegral_const_mul tl tr sb st ((V + H) / 2) (fun p => (u p) ^ 2),
    rectangleIntegral_const_mul tl tr sb st (V / 2) (fun p => (f p) ^ 2)] at hi
  nlinarith

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticRatio
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem actual_elliptic_ratio
    {A B C v : Coord → ℝ} {p : Coord} {d D c Cv M : ℝ}
    (hAd : DifferentiableAt ℝ A p) (hvdiff : DifferentiableAt ℝ v p)
    (hd : 0 < d) (hdD : d ≤ D) (hc : 0 < c) (hCv : 0 ≤ Cv) (hM : 0 ≤ M)
    (hv : 0 < v p) (hvd : v p ≤ d ^ 6)
    (hvt : |coordPartial 0 v p| ≤ Cv * Real.sqrt (v p) * (d ^ 2 + d ^ 3))
    (hvs : |coordPartial 1 v p| ≤ Cv * Real.sqrt (v p) * (d ^ 2 + d ^ 3))
    (hAlo : c * d ≤ A p) (hAhi : |A p| ≤ M)
    (hAs : |coordPartial 1 A p| ≤ M) (hB : |B p| ≤ M) (hC : |C p| ≤ M) :
    (ellipticErrorT B v p) ^ 2 / v p + (ellipticErrorS A C v p) ^ 2 / (A p * v p) ≤
      ellipticRatioConstant D c Cv M := by
  rw [ellipticErrorT, ellipticErrorS, HessianCalculus.coordPartial_mul_at hAd hvdiff 1]
  exact elliptic_ratio_scalar hd hdD hc hCv hM hv hvd hvt hvs hAlo hAhi hAs hB hC

theorem ellipticWeight_partial_bound_common {b c MK X : ℝ}
    {chi K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hMK : 0 ≤ MK) (hX : 0 ≤ X)
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hchiRange : 0 ≤ chi p ∧ chi p ≤ 1) (i : Fin 2)
    (hchii : |coordPartial i chi p| ≤ X) (hKi : |coordPartial i K p| ≤ MK) :
    |coordPartial i (ellipticWeight b c chi K) p| ≤
      ellipticCutoffDerivativeConstant c MK X * Real.sqrt (ellipticWeight b c chi K p) *
        (edgeDistance b p ^ 2 + edgeDistance b p ^ 3) := by
  let P := (2 * transitionDerivativeBound / c) * (MK + c)
  have hP : 0 ≤ P := by
    have htheta := transitionDerivativeBound_pos.le
    dsimp [P]
    positivity
  have hcompare : 3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
      edgeDistance b p ^ 2 * P ≤
      (3 + X + P) * (edgeDistance b p ^ 2 + edgeDistance b p ^ 3) := by
    nlinarith [mul_nonneg hX (sq_nonneg (edgeDistance b p)),
      mul_nonneg hP (pow_pos hd 3).le]
  calc
    _ ≤ 2 * Real.sqrt (ellipticWeight b c chi K p) *
        (3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
          edgeDistance b p ^ 2 * P) :=
      ellipticWeight_partial_bound hc hd hMK hchi hK hchiRange i hchii hKi
    _ ≤ 2 * Real.sqrt (ellipticWeight b c chi K p) *
        ((3 + X + P) * (edgeDistance b p ^ 2 + edgeDistance b p ^ 3)) :=
      mul_le_mul_of_nonneg_left hcompare (by positivity)
    _ = _ := by unfold ellipticCutoffDerivativeConstant; dsimp [P] <;> ring

theorem ellipticCutoff_actual_ratio
    {b c MK X D g0 M : ℝ} {chi K G1 B C : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hMK : 0 ≤ MK) (hX : 0 ≤ X) (hg0 : 0 < g0) (hM : 0 ≤ M)
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hG1 : DifferentiableAt ℝ G1 p)
    (hchiRange : 0 ≤ chi p ∧ chi p ≤ 1)
    (hchii : ∀ i : Fin 2, |coordPartial i chi p| ≤ X)
    (hKi : ∀ i : Fin 2, |coordPartial i K p| ≤ MK)
    (hv : 0 < ellipticWeight b c chi K p) (hGlow : g0 ≤ G1 p)
    (hAhi : |G1 p * K p| ≤ M)
    (hAs : |coordPartial 1 (fun q => G1 q * K q) p| ≤ M)
    (hB : |B p| ≤ M) (hC : |C p| ≤ M) :
    (ellipticErrorT B (ellipticWeight b c chi K) p) ^ 2 /
        ellipticWeight b c chi K p +
      (ellipticErrorS (fun q => G1 q * K q) C (ellipticWeight b c chi K) p) ^ 2 /
        (G1 p * K p * ellipticWeight b c chi K p) ≤
      ellipticRatioConstant D (g0 * c / 2) (ellipticCutoffDerivativeConstant c MK X) M := by
  have hKlo : c / 2 * edgeDistance b p < K p :=
    ellipticWeight_pos_implies_curvature hc (sub_pos.mp hd) hv
  have hKpos : 0 < K p := (mul_pos (by positivity) hd).trans hKlo
  have hAlo : (g0 * c / 2) * edgeDistance b p ≤ G1 p * K p := by
    have hfirst := mul_le_mul_of_nonneg_left hKlo.le hg0.le
    have hsecond := mul_le_mul_of_nonneg_right hGlow hKpos.le
    nlinarith [hfirst, hsecond]
  have hvdiff : DifferentiableAt ℝ (ellipticWeight b c chi K) p := by
    unfold ellipticWeight
    have hdiffer : DifferentiableAt ℝ (edgeDistance b) p :=
      (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
    have hgate : DifferentiableAt ℝ (fun q => ellipticPhi c (K q / edgeDistance b q)) p :=
      ellipticGate_differentiableAt hK hd.ne'
    exact ((hdiffer.pow 6).mul (hchi.pow 2)).mul (hgate.pow 2)
  exact actual_elliptic_ratio (hG1.mul hK) hvdiff hd hdD (by positivity)
    (ellipticCutoffDerivativeConstant_nonneg hc hMK hX) hM hv
    (ellipticWeight_le_distance_six b c chi K p hchiRange)
    (ellipticWeight_partial_bound_common hc hd hMK hX hchi hK hchiRange 0 (hchii 0) (hKi 0))
    (ellipticWeight_partial_bound_common hc hd hMK hX hchi hK hchiRange 1 (hchii 1) (hKi 1))
    hAlo hAhi hAs hB hC

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticApplication
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

theorem threeEdgeDerivativeConstant_nonneg {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) :
    0 ≤ threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1 := by
  have ht := transitionDerivativeBound_pos.le
  have hl := sub_pos.mpr hL
  have hr := sub_pos.mpr hR
  have hs := sub_pos.mpr hS
  unfold threeEdgeDerivativeConstant
  positivity

theorem threeEdge_ellipticWeight_boundary {l0 l1 r1 r0 a0 a1 b c : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (K : Coord → ℝ) :
    zeroRectangleBoundary l0 r0 a0 b
      (ellipticWeightC1 b c (threeEdgeCutoff l0 l1 r1 r0 a0 a1) K) := by
  constructor
  · intro s hs
    have hl := threeEdgeCutoff_zero hL hR hS (boxPoint l0 s)
      (Or.inl (by simp [boxPoint]))
    have hr := threeEdgeCutoff_zero hL hR hS (boxPoint r0 s)
      (Or.inr (Or.inl (by simp [boxPoint])))
    constructor <;> simp [ellipticWeightC1, hl, hr]
  · intro t ht
    have hb := threeEdgeCutoff_zero hL hR hS (boxPoint t a0)
      (Or.inr (Or.inr (by simp [boxPoint])))
    constructor
    · simp [ellipticWeightC1, hb]
    · exact ellipticWeightC1_zero (by simp [boxPoint])

variable {U : Set Coord} {K G1 B C u f : Coord → ℝ}
  {l0 l1 r1 r0 a0 a1 b c MK g0 M : ℝ}

theorem threeEdge_elliptic_energy_bound
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1)
    (ht : l0 ≤ r0) (hs : a0 ≤ b) (hc : 0 < c)
    (hMK : 0 ≤ MK) (hg0 : 0 < g0) (hM : 0 ≤ M)
    (hU : IsOpen U) (hK : ContDiffOn ℝ ∞ K U) (hG1 : ContDiffOn ℝ ∞ G1 U)
    (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle l0 r0 a0 b ⊆ U)
    (hEq : ∀ p ∈ U, multiplierOperator (fun q => G1 q * K q) B C u p = f p)
    (hKi : ∀ p ∈ closedRectangle l0 r0 a0 b, ∀ i : Fin 2, |coordPartial i K p| ≤ MK)
    (hGlow : ∀ p ∈ closedRectangle l0 r0 a0 b, g0 ≤ G1 p)
    (hAhi : ∀ p ∈ closedRectangle l0 r0 a0 b, |G1 p * K p| ≤ M)
    (hAs : ∀ p ∈ closedRectangle l0 r0 a0 b,
      |coordPartial 1 (fun q => G1 q * K q) p| ≤ M)
    (hBb : ∀ p ∈ closedRectangle l0 r0 a0 b, |B p| ≤ M)
    (hCb : ∀ p ∈ closedRectangle l0 r0 a0 b, |C p| ≤ M) :
    rectangleIntegral l0 r0 a0 b
      (ellipticEnergy (fun q => G1 q * K q)
        (ellipticWeight b c (threeEdgeCutoff l0 l1 r1 r0 a0 a1) K) u) ≤
      (b - a0) ^ 6 * rectangleIntegral l0 r0 a0 b (fun p => (f p) ^ 2) +
        ((b - a0) ^ 6 + ellipticRatioConstant (b - a0) (g0 * c / 2)
          (ellipticCutoffDerivativeConstant c MK (threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1)) M) *
          rectangleIntegral l0 r0 a0 b (fun p => (u p) ^ 2) := by
  let chi := threeEdgeCutoff l0 l1 r1 r0 a0 a1
  let v := ellipticWeightC1 b c chi K
  let X := threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1
  let H := ellipticRatioConstant (b - a0) (g0 * c / 2) (ellipticCutoffDerivativeConstant c MK X) M
  have hX : 0 ≤ X := threeEdgeDerivativeConstant_nonneg hL hR hS
  have hchi : ContDiffOn ℝ ∞ chi U := (threeEdgeCutoff_contDiff _ _ _ _ _ _).contDiffOn
  have hv : ContDiffOn ℝ 1 v U := ellipticWeightC1_contDiffOn hc
    (hchi.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hK.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hA : ContDiffOn ℝ ∞ (fun q => G1 q * K q) U := hG1.mul hK
  have hH : 0 ≤ H := ellipticRatioConstant_nonneg (sub_nonneg.mpr hs) (by positivity) hM
  have hposD (p : Coord) (hpv : 0 < v p) : p 1 < b := by
    by_contra hn
    have hz : v p = 0 := ellipticWeightC1_zero (le_of_not_gt hn)
    linarith
  have hweightEq (p : Coord) (hp : p ∈ closedRectangle l0 r0 a0 b) :
      v p = ellipticWeight b c chi K p := ellipticWeightC1_eq hp.2.2
  have hposA (p : Coord) (hp : p ∈ closedRectangle l0 r0 a0 b) (hpv : 0 < v p) :
      0 < G1 p * K p := by
    have hd := hposD p hpv
    have hcurv := ellipticWeight_pos_implies_curvature hc hd
      (show 0 < ellipticWeight b c chi K p by simpa only [← hweightEq p hp] using hpv)
    have hKpos : 0 < K p := (mul_pos (by positivity : 0 < c / 2) (sub_pos.mpr hd)).trans hcurv
    exact mul_pos (hg0.trans_le (hGlow p hp)) hKpos
  have hratio (p : Coord) (hp : p ∈ closedRectangle l0 r0 a0 b) (hpv : 0 < v p) :
      (ellipticErrorT B v p) ^ 2 / v p +
        (ellipticErrorS (fun q => G1 q * K q) C v p) ^ 2 / (G1 p * K p * v p) ≤ H := by
    have hd := hposD p hpv
    have herrors := ellipticWeightC1_errors_eq (c := c) (fun q => G1 q * K q) B C chi K hd
    change (ellipticErrorT B (ellipticWeightC1 b c chi K) p) ^ 2 / v p +
      (ellipticErrorS (fun q => G1 q * K q) C (ellipticWeightC1 b c chi K) p) ^ 2 /
        (G1 p * K p * v p) ≤ H
    rw [herrors.1, herrors.2, hweightEq p hp]
    exact ellipticCutoff_actual_ratio hc (sub_pos.mpr hd)
      (by unfold edgeDistance; linarith [hp.2.1]) hMK hX hg0 hM
      ((hchi.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      ((hK.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      ((hG1.contDiffAt (hU.mem_nhds (hbox hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (threeEdgeCutoff_range _ _ _ _ _ _ p)
      (threeEdgeCutoff_partial_common hL hR hS p) (hKi p hp)
      (show 0 < ellipticWeight b c chi K p by simpa only [← hweightEq p hp] using hpv)
      (hGlow p hp) (hAhi p hp) (hAs p hp) (hBb p hp) (hCb p hp)
  have hestimate := integrated_elliptic_energy_bound_C1 ht hs hU hA hB hC hv hu hbox
    (threeEdge_ellipticWeight_boundary hL hR hS K) hEq ((b - a0) ^ 6) H
    (by positivity) hH (fun p _ => ellipticWeightC1_nonneg _ _ _ _ p)
    (fun p hp => (ellipticWeightC1_le_distance_six _ _ _ _ p
      (threeEdgeCutoff_range _ _ _ _ _ _ p)).trans
        (pow_le_pow_left₀ (sub_nonneg.mpr hp.2.2)
          (by linarith [hp.2.1]) 6))
    hposA hratio
  have henergyEq : rectangleIntegral l0 r0 a0 b
      (ellipticEnergy (fun q => G1 q * K q) v u) =
      rectangleIntegral l0 r0 a0 b
        (ellipticEnergy (fun q => G1 q * K q) (ellipticWeight b c chi K) u) := by
    apply rectangleIntegral_congr ht hs
    intro p hp
    change v p * _ = ellipticWeight b c chi K p * _
    rw [hweightEq p hp]
  rw [henergyEq] at hestimate
  exact hestimate

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapAreaFormula
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev

theorem cap_image_integral_formula
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st)) :
    (∫ p in capChart Y '' closedRectangle tl tr sb st, f p) =
      rectangleIntegral tl tr sb st (fun p => coordPartial 1 (capFlowHeight Y) p*capPullback Y f p) := by
  have hrect : MeasurableSet (closedRectangle tl tr sb st) := (capRectangle_isCompact _ _ _ _).isClosed.measurableSet
  have hchart := capChart_contDiffOn hYs
  have hd (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :
      HasFDerivWithinAt (capChart Y) (fderiv ℝ (capChart Y) p) (closedRectangle tl tr sb st) p :=
    ((hchart.contDiffAt (capChartDomain_isOpen.mem_nhds (hbox hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.hasFDerivWithinAt
  have hinj := (capChart_injOn_of_pairChart hsource heq).mono hbox
  have hcomp : ContinuousOn (capPullback Y f) (closedRectangle tl tr sb st) :=
    hf.comp (hchart.continuousOn.mono hbox) (fun p hp => ⟨p,hp,rfl⟩)
  have hJ : ContinuousOn (coordPartial 1 (capFlowHeight Y)) (closedRectangle tl tr sb st) :=
    (partial_contDiffOn (capFlowHeight_contDiffOn hYs) capChartDomain_isOpen 1).continuousOn.mono hbox
  calc
    _ = ∫ p in closedRectangle tl tr sb st, |(fderiv ℝ (capChart Y) p).det| • f (capChart Y p) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume hrect hd hinj f
    _ = ∫ p in closedRectangle tl tr sb st, coordPartial 1 (capFlowHeight Y) p*capPullback Y f p := by
      apply setIntegral_congr_fun hrect
      intro p hp
      change |(fderiv ℝ (capChart Y) p).det| * f (capChart Y p) = _
      rw [capChart_abs_det_fderiv hYs hvar (hbox hp)]
      rfl
    _ = _ := (rectangleIntegral_eq_coordinate_closed_area ht hs (hJ.mul hcomp)).symm

theorem cap_rectangle_square_integral_bounds
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st)) :
    Real.exp (-2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) ≤
      ∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2 ∧
    (∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) ≤
      Real.exp (2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) := by
  have hchart := capChart_contDiffOn hYs
  have hfc : ContinuousOn (fun p => (capPullback Y f p)^2) (closedRectangle tl tr sb st) :=
    (hf.comp (hchart.continuousOn.mono hbox) (fun p hp => ⟨p,hp,rfl⟩)).pow 2
  have hJc : ContinuousOn (coordPartial 1 (capFlowHeight Y)) (closedRectangle tl tr sb st) :=
    (partial_contDiffOn (capFlowHeight_contDiffOn hYs) capChartDomain_isOpen 1).continuousOn.mono hbox
  have hformula := cap_image_integral_formula hYs hvar hsource heq ht hs hbox (hf.pow 2)
  change (∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) =
    rectangleIntegral tl tr sb st (fun p => coordPartial 1 (capFlowHeight Y) p*(capPullback Y f p)^2) at hformula
  rw [hformula]
  constructor
  · have hh := rectangleIntegral_mono ht hs (continuousOn_const.mul hfc) (hJc.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).1 (sq_nonneg _))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh
  · have hh := rectangleIntegral_mono ht hs (hJc.mul hfc) (continuousOn_const.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).2 (sq_nonneg _))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh

theorem cap_pullback_square_integral_le_image
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) ≤
      Real.exp (2*M)*(∫ p in capChart Y '' closedRectangle tl tr sb st, (f p)^2) := by
  have hh := (cap_rectangle_square_integral_bounds hYs hvar hsource heq ht hs hbox hJ hf).1
  have hscale : Real.exp (2*M)*Real.exp (-2*M) = 1 := by rw [←Real.exp_add]; simp
  calc
    _ = Real.exp (2*M)*(Real.exp (-2*M)*rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2)) := by
      rw [←mul_assoc,hscale,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapDensityBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem cap_rectangle_density_integral_bounds
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st))
    (hf0 : ∀ p ∈ capChart Y '' closedRectangle tl tr sb st, 0 ≤ f p) :
    Real.exp (-2*M)*rectangleIntegral tl tr sb st (capPullback Y f) ≤
      (∫ p in capChart Y '' closedRectangle tl tr sb st, f p) ∧
    (∫ p in capChart Y '' closedRectangle tl tr sb st, f p) ≤
      Real.exp (2*M)*rectangleIntegral tl tr sb st (capPullback Y f) := by
  have hfc : ContinuousOn (capPullback Y f) (closedRectangle tl tr sb st) :=
    hf.comp ((capChart_contDiffOn hYs).continuousOn.mono hbox) (fun p hp => ⟨p,hp,rfl⟩)
  have hJc : ContinuousOn (coordPartial 1 (capFlowHeight Y)) (closedRectangle tl tr sb st) :=
    (partial_contDiffOn (capFlowHeight_contDiffOn hYs) capChartDomain_isOpen 1).continuousOn.mono hbox
  rw [cap_image_integral_formula hYs hvar hsource heq ht hs hbox hf]
  constructor
  · have hh := rectangleIntegral_mono ht hs (continuousOn_const.mul hfc) (hJc.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).1 (hf0 _ ⟨p,hp,rfl⟩))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh
  · have hh := rectangleIntegral_mono ht hs (hJc.mul hfc) (continuousOn_const.mul hfc)
      (fun p hp => mul_le_mul_of_nonneg_right (hJ p hp).2 (hf0 _ ⟨p,hp,rfl⟩))
    simpa only [Pi.mul_def, rectangleIntegral_const_mul] using hh

theorem cap_pullback_density_integral_le_image
    {Y : ℝ → ℝ → ℝ} {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    {f : Coord → ℝ} (hf : ContinuousOn f (capChart Y '' closedRectangle tl tr sb st))
    (hf0 : ∀ p ∈ capChart Y '' closedRectangle tl tr sb st, 0 ≤ f p) :
    rectangleIntegral tl tr sb st (capPullback Y f) ≤
      Real.exp (2*M)*(∫ p in capChart Y '' closedRectangle tl tr sb st, f p) := by
  have hh := (cap_rectangle_density_integral_bounds hYs hvar hsource heq ht hs hbox hJ hf hf0).1
  have hscale : Real.exp (2*M)*Real.exp (-2*M) = 1 := by
    rw [←Real.exp_add,show 2*M+(-2*M) = 0 by ring,Real.exp_zero]
  calc
    _ = Real.exp (2*M)*(Real.exp (-2*M)*rectangleIntegral tl tr sb st (capPullback Y f)) := by
      rw [←mul_assoc,hscale,one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (Real.exp_pos _).le

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapFlowCoordinateJets
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem coordPartial_time_of_pair_eq {f : Coord → ℝ} {F : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f capChartDomain)
    (he : ∀ p ∈ capChartDomain, f p = F (p 0, p 1))
    {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 0 f p = deriv (fun t => F (t, p 1)) (p 0) := by
  have hd := ((hf.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hp' : boxPoint (p 0) (p 1) = p := boxPoint_coord_eta p
  have hd' : HasFDerivAt f (fderiv ℝ f p) (boxPoint (p 0) (p 1)) := by rw [hp']; exact hd
  have hline := hd'.comp_hasDerivAt (p 0) (boxPoint_hasDerivAt_t (p 0) (p 1))
  have hevent : (fun t => F (t, p 1)) =ᶠ[𝓝 (p 0)] (fun t => f (boxPoint t (p 1))) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.1] with t ht
    have hm : boxPoint t (p 1) ∈ capChartDomain := by
      simpa [capChartDomain, coordinateRectangle, boxPoint] using And.intro ht hp.2
    simpa [boxPoint] using (he (boxPoint t (p 1)) hm).symm
  exact (hline.congr_of_eventuallyEq hevent).deriv.symm

theorem coordPartial_initial_of_pair_eq {f : Coord → ℝ} {F : ℝ × ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f capChartDomain)
    (he : ∀ p ∈ capChartDomain, f p = F (p 0, p 1))
    {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 1 f p = deriv (fun s => F (p 0, s)) (p 1) := by
  have hd := ((hf.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hp' : boxPoint (p 0) (p 1) = p := boxPoint_coord_eta p
  have hd' : HasFDerivAt f (fderiv ℝ f p) (boxPoint (p 0) (p 1)) := by rw [hp']; exact hd
  have hline := hd'.comp_hasDerivAt (p 1) (boxPoint_hasDerivAt_s (p 0) (p 1))
  have hevent : (fun s => F (p 0, s)) =ᶠ[𝓝 (p 1)] (fun s => f (boxPoint (p 0) s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hp.2] with s hs
    have hm : boxPoint (p 0) s ∈ capChartDomain := by
      simpa [capChartDomain, coordinateRectangle, boxPoint] using And.intro hp.1 hs
    simpa [boxPoint] using (he (boxPoint (p 0) s) hm).symm
  exact (hline.congr_of_eventuallyEq hevent).deriv.symm

section HeightWords
variable {Y : ℝ → ℝ → ℝ}
variable (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
include hY

theorem capFlowHeight_partial_zero_eq {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 0 (capFlowHeight Y) p = timeFlowDerivative Y (p 0, p 1) :=
  (capFlowHeight_hasDerivAt_time hY hp).deriv.symm

theorem capFlowHeight_partial_one_eq {p : Coord} (hp : p ∈ capChartDomain) :
    coordPartial 1 (capFlowHeight Y) p = initialFlowDerivative Y (p 0, p 1) :=
  (capFlowHeight_hasDerivAt_initial hY hp).deriv.symm

theorem capFlowHeight_word_00 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [0, 0] (capFlowHeight Y) p = timeSecondFlowDerivative Y (p 0, p 1) :=
  coordPartial_time_of_pair_eq
    (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 0)
    (fun _ hx => capFlowHeight_partial_zero_eq hY hx) hp

theorem capFlowHeight_word_10 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 0] (capFlowHeight Y) p = mixedFlowDerivative Y (p 0, p 1) :=
  coordPartial_initial_of_pair_eq
    (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 0)
    (fun _ hx => capFlowHeight_partial_zero_eq hY hx) hp

theorem capFlowHeight_word_11 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 1] (capFlowHeight Y) p = initialSecondFlowDerivative Y (p 0, p 1) :=
  coordPartial_initial_of_pair_eq
    (partial_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen 1)
    (fun _ hx => capFlowHeight_partial_one_eq hY hx) hp

theorem capFlowHeight_word_000 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [0, 0, 0] (capFlowHeight Y) p =
      deriv (fun t => timeSecondFlowDerivative Y (t, p 1)) (p 0) :=
  coordPartial_time_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [0, 0])
    (fun _ hx => capFlowHeight_word_00 hY hx) hp

theorem capFlowHeight_word_100 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 0, 0] (capFlowHeight Y) p =
      deriv (fun s => timeSecondFlowDerivative Y (p 0, s)) (p 1) :=
  coordPartial_initial_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [0, 0])
    (fun _ hx => capFlowHeight_word_00 hY hx) hp

theorem capFlowHeight_word_110 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 1, 0] (capFlowHeight Y) p =
      deriv (fun s => mixedFlowDerivative Y (p 0, s)) (p 1) :=
  coordPartial_initial_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [1, 0])
    (fun _ hx => capFlowHeight_word_10 hY hx) hp

theorem capFlowHeight_word_111 {p : Coord} (hp : p ∈ capChartDomain) :
    iteratedCoordPartial [1, 1, 1] (capFlowHeight Y) p =
      deriv (fun s => initialSecondFlowDerivative Y (p 0, s)) (p 1) :=
  coordPartial_initial_of_pair_eq
    (LowQuotient.iterated_contDiffOn (capFlowHeight_contDiffOn hY) capChartDomain_isOpen [1, 1])
    (fun _ hx => capFlowHeight_word_11 hY hx) hp

end HeightWords

theorem iterated_three_swap_outer {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] f p = iteratedCoordPartial [j, i, k] f p :=
  coordPartial_comm (partial_contDiffOn hf hU k) hU hp i j

theorem iterated_three_swap_inner {f : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) {p : Coord} (hp : p ∈ U) (i j k : Fin 2) :
    iteratedCoordPartial [i, j, k] f p = iteratedCoordPartial [i, k, j] f p := by
  have he : coordPartial j (coordPartial k f) =ᶠ[𝓝 p] coordPartial k (coordPartial j f) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact coordPartial_comm hf hU hx j k
  exact coordPartial_eq_of_eventuallyEq he i

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapFlowJetBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
variable (hM : 0 ≤ M)
variable (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
variable (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
variable (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
variable (hq3 : ∀ i j k : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j (coordPartial k q)) p| ≤ M)
include hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3

omit hq2 hq3 in
theorem capFlowHeight_word_one_bound
    (_ : ∀ first second : Fin 2, ∀ point ∈ modelSquare,
      |coordPartial first (coordPartial second q) point| ≤ M)
    (_ : ∀ first second third : Fin 2, ∀ point ∈ modelSquare,
      |coordPartial first (coordPartial second (coordPartial third q)) point| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) (i : Fin 2) :
    |iteratedCoordPartial [i] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  obtain ⟨_, h1, hV, _⟩ := flowCoordinateBound_dominates hM
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one]
  · rw [show iteratedCoordPartial [0] (capFlowHeight Y) p = timeFlowDerivative Y (p 0, p 1) from
      capFlowHeight_partial_zero_eq hs hp]
    exact (cap_flow_time_bound hq hU hSU hY hrange hstart hode hq0 hp.2 hp.1).trans
      ((by norm_num : (1 : ℝ) / 100 ≤ 1).trans h1)
  · rw [show iteratedCoordPartial [1] (capFlowHeight Y) p = initialFlowDerivative Y (p 0, p 1) from
      capFlowHeight_partial_one_eq hs hp, initialFlowDerivative,
      abs_of_pos (cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hp.2 hp.1)]
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hp.2 hp.1).2.trans hV

omit hq3 in
theorem capFlowHeight_word_two_bound
    (_ : ∀ first second third : Fin 2, ∀ point ∈ modelSquare,
      |coordPartial first (coordPartial second (coordPartial third q)) point| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) (i j : Fin 2) :
    |iteratedCoordPartial [i, j] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hf := capFlowHeight_contDiffOn hs
  obtain ⟨_, _, _, htt, hts, hss, _⟩ := flowCoordinateBound_dominates hM
  have hqweak (p : Coord) (hp : p ∈ modelSquare) : |q p| ≤ 1 :=
    (hq0 p hp).trans (by norm_num)
  have h00 : |iteratedCoordPartial [0, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_00 hs hp]
    exact (cap_flow_time_second_bound hq hU hSU hY hrange hstart hode hM hqweak hq1 hp.2 hp.1).trans htt
  have h10 : |iteratedCoordPartial [1, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_10 hs hp]
    exact (cap_flow_mixed_bound hq hU hSU hY hrange hstart hode hM hq1 hp.2 hp.1).trans hts
  have h11 : |iteratedCoordPartial [1, 1] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_11 hs hp]
    exact (cap_flow_initial_second_bound hq hU hSU hY hrange hstart hode hM (hq1 1) (hq2 1 1) hp.2 hp.1).trans hss
  fin_cases i <;> fin_cases j <;> simp only [Fin.mk_zero, Fin.mk_one]
  · exact h00
  · have he : iteratedCoordPartial [0, 1] (capFlowHeight Y) p = iteratedCoordPartial [1, 0] (capFlowHeight Y) p :=
      coordPartial_comm hf capChartDomain_isOpen hp 0 1
    rw [he]; exact h10
  · exact h10
  · exact h11

theorem capFlowHeight_word_three_bound {p : Coord} (hp : p ∈ capChartDomain) (i j k : Fin 2) :
    |iteratedCoordPartial [i, j, k] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hf := capFlowHeight_contDiffOn hs
  obtain ⟨_, _, _, _, _, _, httt, htts, htss, hsss⟩ := flowCoordinateBound_dominates hM
  have hqweak (p : Coord) (hp : p ∈ modelSquare) : |q p| ≤ 1 :=
    (hq0 p hp).trans (by norm_num)
  have h000 : |iteratedCoordPartial [0, 0, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_000 hs hp]
    exact (cap_flow_time_third_bound hq hU hSU hY hrange hstart hode hM hqweak hq1 hq2 hp.2 hp.1).trans httt
  have h100 : |iteratedCoordPartial [1, 0, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_100 hs hp]
    exact (cap_flow_time_second_initial_bound hq hU hSU hY hrange hstart hode hM hqweak hq1 hq2 hp.2 hp.1).trans htts
  have h110 : |iteratedCoordPartial [1, 1, 0] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_110 hs hp]
    exact (cap_flow_mixed_initial_bound hq hU hSU hY hrange hstart hode hM hq1 hq2 hp.2 hp.1).trans htss
  have h111 : |iteratedCoordPartial [1, 1, 1] (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
    rw [capFlowHeight_word_111 hs hp]
    exact (cap_flow_initial_third_bound hq hU hSU hY hrange hstart hode hM (hq1 1) (hq2 1 1) (hq3 1 1 1) hp.2 hp.1).trans hsss
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [Fin.mk_zero, Fin.mk_one]
  · exact h000
  · rw [iterated_three_swap_inner hf capChartDomain_isOpen hp 0 0 1,
      iterated_three_swap_outer hf capChartDomain_isOpen hp 0 1 0]
    exact h100
  · rw [iterated_three_swap_outer hf capChartDomain_isOpen hp 0 1 0]
    exact h100
  · rw [iterated_three_swap_outer hf capChartDomain_isOpen hp 0 1 1,
      iterated_three_swap_inner hf capChartDomain_isOpen hp 1 0 1]
    exact h110
  · exact h100
  · rw [iterated_three_swap_inner hf capChartDomain_isOpen hp 1 0 1]
    exact h110
  · exact h110
  · exact h111

theorem capFlowHeight_coordinate_bound :
    CoordinateBound (capFlowHeight Y) capChartDomain 3 (flowCoordinateBound M) := by
  intro ds hds p hp
  cases ds with
  | nil =>
    have hh : |capFlowHeight Y p| ≤ 3 := abs_le.mpr
      (hrange (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩)
    exact hh.trans (flowCoordinateBound_dominates hM).1
  | cons i ds =>
    cases ds with
    | nil => exact capFlowHeight_word_one_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3 hp i
    | cons j ds =>
      cases ds with
      | nil => exact capFlowHeight_word_two_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3 hp i j
      | cons k ds =>
        cases ds with
        | nil => exact capFlowHeight_word_three_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3 hp i j k
        | cons l ds => simp only [List.length_cons] at hds; omega

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapFlowUniqueness
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capChart_eqOn_of_same_ode
    {q : Coord → ℝ} {U : Set Coord} {Y Z : ℝ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hYstart : ∀ s ∈ Icc (-2:ℝ) 2, Y s 0 = s)
    (hYode : ∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2:ℝ) 2) t)
    (hYdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50)
    (hZstart : ∀ s ∈ Icc (-2:ℝ) 2, Z s 0 = s)
    (hZode : ∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
      HasDerivWithinAt (Z s) (-q (coordinatePoint t (Z s t))) (Icc (-2:ℝ) 2) t)
    (hZdisp : ∀ p ∈ capChartDomain, |capFlowHeight Z p-p 1| ≤ (1:ℝ)/50) :
    EqOn (capChart Y) (capChart Z) capChartDomain := by
  obtain ⟨K,hK⟩ := exists_flowField_lipschitz hq hU hSU
  have hsame (s : ℝ) (hs : s ∈ Ioo (-2:ℝ) 2) : EqOn (Y s) (Z s) (Ioo (-2:ℝ) 2) := by
    have hs' : s ∈ Icc (-2:ℝ) 2 := ⟨hs.1.le,hs.2.le⟩
    apply ODE_solution_unique_of_mem_Ioo
      (v := flowField q) (s := fun _ => closedBall (0:ℝ) 3)
      (fun t ht => hK t ⟨ht.1.le,ht.2.le⟩) (t₀ := 0) (by norm_num)
    · intro t ht
      exact ⟨(hYode s hs' t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2),
        cap_trajectory_mem_ball_of_displacement hYdisp hs ht⟩
    · intro t ht
      exact ⟨(hZode s hs' t ⟨ht.1.le,ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2),
        cap_trajectory_mem_ball_of_displacement hZdisp hs ht⟩
    · rw [hYstart s hs',hZstart s hs']
  intro p hp
  unfold capChart capFlowHeight
  rw [hsame (p 1) hp.2 hp.1]

theorem capPullback_eventuallyEq_of_chart_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (f : Coord → ℝ) {p : Coord} (hp : p ∈ capChartDomain) :
    capPullback Y f =ᶠ[𝓝 p] capPullback Z f := by
  filter_upwards [capChartDomain_isOpen.mem_nhds hp] with r hr
  exact congrArg f (heq hr)

theorem capPullback_square_rectangle_eq_of_chart_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (f : Coord → ℝ) {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    rectangleIntegral tl tr sb st (fun p => (capPullback Y f p)^2) =
      rectangleIntegral tl tr sb st (fun p => (capPullback Z f p)^2) := by
  apply rectangleIntegral_congr ht hs
  intro p hp
  exact congrArg (fun x : Coord => (f x)^2) (heq (hbox hp))

theorem capPullback_gradient_rectangle_eq_of_chart_eqOn {Y Z : ℝ → ℝ → ℝ}
    (heq : EqOn (capChart Y) (capChart Z) capChartDomain)
    (f : Coord → ℝ) {tl tr sb st : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    rectangleIntegral tl tr sb st (fun p => (coordPartial 0 (capPullback Y f) p)^2+
        (coordPartial 1 (capPullback Y f) p)^2) =
      rectangleIntegral tl tr sb st (fun p => (coordPartial 0 (capPullback Z f) p)^2+
        (coordPartial 1 (capPullback Z f) p)^2) := by
  apply rectangleIntegral_congr ht hs
  intro p hp
  change (coordPartial 0 (capPullback Y f) p)^2 + (coordPartial 1 (capPullback Y f) p)^2 =
    (coordPartial 0 (capPullback Z f) p)^2 + (coordPartial 1 (capPullback Z f) p)^2
  rw [coordPartial_eq_of_eventuallyEq (capPullback_eventuallyEq_of_chart_eqOn heq f (hbox hp)) 0,
    coordPartial_eq_of_eventuallyEq (capPullback_eventuallyEq_of_chart_eqOn heq f (hbox hp)) 1]

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapGradientTransport
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capPullback_gradient_pointwise
    {Y : ℝ → ℝ → ℝ} {q f : Coord → ℝ} {M : ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hf : DifferentiableAt ℝ f (capChart Y p))
    (hq : |q (capChart Y p)| ≤ 1)
    (hJ : Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
      coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M)) :
    coordinateGradientSquare (capPullback Y f) p ≤
      (2+(Real.exp (2*M))^2)*capPullback Y (coordinateGradientSquare f) p ∧
    capPullback Y (coordinateGradientSquare f) p ≤
      (2+3*(Real.exp (2*M))^2)*coordinateGradientSquare (capPullback Y f) p := by
  have hJpos : 0 < coordPartial 1 (capFlowHeight Y) p := (Real.exp_pos _).trans_le hJ.1
  have hJinv : 1/Real.exp (2*M) ≤ coordPartial 1 (capFlowHeight Y) p := by
    simpa only [show -2*M = -(2*M) by ring,Real.exp_neg,one_div] using hJ.1
  have htime := capPullback_partial_time hYs hode hp hf
  have hinit := capPullback_partial_initial hYs hp hf
  change (coordPartial 0 (capPullback Y f) p)^2+(coordPartial 1 (capPullback Y f) p)^2 ≤
      (2+(Real.exp (2*M))^2)*((coordPartial 0 f (capChart Y p))^2+(coordPartial 1 f (capChart Y p))^2) ∧
    (coordPartial 0 f (capChart Y p))^2+(coordPartial 1 f (capChart Y p))^2 ≤
      (2+3*(Real.exp (2*M))^2)*((coordPartial 0 (capPullback Y f) p)^2+(coordPartial 1 (capPullback Y f) p)^2)
  rw [htime,hinit]
  simp only [coordinateDrift,capPullback]
  have ha : |-q (capChart Y p)| ≤ 1 := by simpa only [abs_neg] using hq
  constructor
  · simpa only [neg_mul,sub_eq_add_neg,mul_comm] using
      triangular_gradient_forward_scalar (x := coordPartial 0 f (capChart Y p))
        (y := coordPartial 1 f (capChart Y p)) ha hJpos.le hJ.2
  · simpa only [neg_mul,sub_eq_add_neg,mul_comm] using
      triangular_gradient_inverse_scalar (x := coordPartial 0 f (capChart Y p))
        (y := coordPartial 1 f (capChart Y p)) ha (Real.exp_pos _) hJinv

theorem cap_gradient_integral_bounds
    {Y : ℝ → ℝ → ℝ} {q f : Coord → ℝ} {V : Set Coord}
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V)
    (hmap : MapsTo (capChart Y) capChartDomain V)
    {tl tr sb st M : ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hq : ∀ p ∈ closedRectangle tl tr sb st, |q (capChart Y p)| ≤ 1)
    (hJ : ∀ p ∈ closedRectangle tl tr sb st,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M)) :
    rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f)) ≤
      ((2+(Real.exp (2*M))^2)*Real.exp (2*M))*
        (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p) ∧
    (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p) ≤
      (Real.exp (2*M)*(2+3*(Real.exp (2*M))^2))*
        rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f)) := by
  have hGp := coordinateGradientSquare_contDiffOn hf hV
  have hGc : ContinuousOn (coordinateGradientSquare f) (capChart Y '' closedRectangle tl tr sb st) :=
    hGp.continuousOn.mono (by rintro _ ⟨p,hp,rfl⟩; exact hmap (hbox hp))
  have hP : ContDiffOn ℝ ∞ (capPullback Y f) capChartDomain := capPullback_contDiffOn hYs hf hmap
  have hGPc : ContinuousOn (coordinateGradientSquare (capPullback Y f)) (closedRectangle tl tr sb st) :=
    (coordinateGradientSquare_contDiffOn hP capChartDomain_isOpen).continuousOn.mono hbox
  have hPGc : ContinuousOn (capPullback Y (coordinateGradientSquare f)) (closedRectangle tl tr sb st) :=
    (capPullback_contDiffOn hYs hGp hmap).continuousOn.mono hbox
  have hpoint (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :=
    capPullback_gradient_pointwise hYs hode (hbox hp)
      ((hf.contDiffAt (hV.mem_nhds (hmap (hbox hp)))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hq p hp) (hJ p hp)
  have hzero := fun p (_hp : p ∈ capChart Y '' closedRectangle tl tr sb st) =>
    coordinateGradientSquare_nonneg f p
  have hforward := rectangleIntegral_mono ht hs hGPc (continuousOn_const.mul hPGc)
    (fun p hp => (hpoint p hp).1)
  simp only [Pi.mul_def, rectangleIntegral_const_mul] at hforward
  have hinverse := rectangleIntegral_mono ht hs hPGc (continuousOn_const.mul hGPc)
    (fun p hp => (hpoint p hp).2)
  simp only [Pi.mul_def, rectangleIntegral_const_mul] at hinverse
  have hlower := cap_pullback_density_integral_le_image hYs hvar hsource heq ht hs hbox hJ hGc hzero
  have hupper := (cap_rectangle_density_integral_bounds hYs hvar hsource heq ht hs hbox hJ hGc hzero).2
  constructor
  · calc
      _ ≤ (2+(Real.exp (2*M))^2)*rectangleIntegral tl tr sb st
          (capPullback Y (coordinateGradientSquare f)) := hforward
      _ ≤ (2+(Real.exp (2*M))^2)*(Real.exp (2*M)*
          (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare f p)) :=
        mul_le_mul_of_nonneg_left hlower (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ Real.exp (2*M)*rectangleIntegral tl tr sb st
          (capPullback Y (coordinateGradientSquare f)) := hupper
      _ ≤ Real.exp (2*M)*((2+3*(Real.exp (2*M))^2)*
          rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y f))) :=
        mul_le_mul_of_nonneg_left hinverse (Real.exp_pos _).le
      _ = _ := by ring

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapReciprocalBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem negative_over_cube_partial {f v : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (hv : DifferentiableAt ℝ v p) (hne : v p ≠ 0) (i : Fin 2) :
    coordPartial i (fun x => -f x / (v x)^3) p =
      -coordPartial i f p / (v p)^3 + 3 * f p * coordPartial i v p / (v p)^4 := by
  have hn : DifferentiableAt ℝ (fun x => -f x) p := hf.neg
  have hp : DifferentiableAt ℝ (fun x => (v x)^3) p := hv.pow 3
  rw [coordPartial_div hn hp (pow_ne_zero 3 hne) i]
  have hneg : coordPartial i (fun x => -f x) p = -coordPartial i f p := by simp [coordPartial]
  have hpow : coordPartial i (fun x => (v x)^3) p = 3 * (v p)^2 * coordPartial i v p := by
    unfold coordPartial
    rw [(hv.hasFDerivAt.pow 3).fderiv]
    norm_num [smul_apply, smul_eq_mul]
  rw [hneg, hpow]
  field_simp [hne]
  ring

theorem capChartRho_partial {Y : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hpos : 0 < coordPartial 1 (capFlowHeight Y) p) (i : Fin 2) :
    coordPartial i (capChartRho Y) p =
      -coordPartial i (coordPartial 1 (capFlowHeight Y)) p /
        (coordPartial 1 (capFlowHeight Y) p)^2 := by
  have hV := ((partial_contDiffOn hF capChartDomain_isOpen 1).contDiffAt
    (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change coordPartial i (fun x => (1 : ℝ) / coordPartial 1 (capFlowHeight Y) x) p = _
  rw [coordPartial_div (differentiableAt_const (1 : ℝ)) hV hpos.ne' i]
  simp [coordPartial]

theorem capChartSigma_partial {Y : ℝ → ℝ → ℝ}
    (hF : ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain)
    {p : Coord} (hp : p ∈ capChartDomain)
    (hpos : 0 < coordPartial 1 (capFlowHeight Y) p) (i : Fin 2) :
    coordPartial i (capChartSigma Y) p =
      -coordPartial i (coordPartial 1 (coordPartial 1 (capFlowHeight Y))) p /
        (coordPartial 1 (capFlowHeight Y) p)^3 +
      3 * coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p *
        coordPartial i (coordPartial 1 (capFlowHeight Y)) p /
        (coordPartial 1 (capFlowHeight Y) p)^4 := by
  have hV := partial_contDiffOn hF capChartDomain_isOpen 1
  have hW := partial_contDiffOn hV capChartDomain_isOpen 1
  exact negative_over_cube_partial
    ((hW.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hV.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hpos.ne' i

theorem capReciprocal_bounds_of_jets {Y : ℝ → ℝ → ℝ} {C c : ℝ}
    (hF : ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain)
    (hC : 0 ≤ C) (hc : 0 < c)
    (hFB : CoordinateBound (capFlowHeight Y) capChartDomain 3 C)
    (hVlower : ∀ p ∈ capChartDomain, c ≤ coordPartial 1 (capFlowHeight Y) p)
    {p : Coord} (hp : p ∈ capChartDomain) :
    0 < capChartRho Y p ∧ |capChartRho Y p| ≤ 1 / c ∧
    (∀ i : Fin 2, |coordPartial i (capChartRho Y) p| ≤ C / c^2) ∧
    |capChartSigma Y p| ≤ C / c^3 ∧
    (∀ i : Fin 2, |coordPartial i (capChartSigma Y) p| ≤ C / c^3 + 3 * C^2 / c^4) := by
  have hVp : 0 < coordPartial 1 (capFlowHeight Y) p := hc.trans_le (hVlower p hp)
  have hpow (n : ℕ) : c^n ≤ |(coordPartial 1 (capFlowHeight Y) p)^n| := by
    rw [abs_pow, abs_of_pos hVp]
    exact pow_le_pow_left₀ hc.le (hVlower p hp) n
  have hW : |coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p| ≤ C :=
    hFB [1, 1] (by norm_num) p hp
  have hVi (i : Fin 2) : |coordPartial i (coordPartial 1 (capFlowHeight Y)) p| ≤ C :=
    hFB [i, 1] (by norm_num) p hp
  have hWi (i : Fin 2) : |coordPartial i (coordPartial 1 (coordPartial 1 (capFlowHeight Y))) p| ≤ C :=
    hFB [i, 1, 1] (by norm_num) p hp
  refine ⟨one_div_pos.mpr hVp, ?_, ?_, ?_, ?_⟩
  · exact LowQuotient.abs_div_bound (by norm_num) (by norm_num : |(1 : ℝ)| ≤ 1) hc
      (by simpa only [abs_of_pos hVp] using hVlower p hp)
  · intro i
    rw [capChartRho_partial hF hp hVp i]
    exact LowQuotient.abs_div_bound hC (by simpa only [abs_neg] using hVi i)
      (pow_pos hc 2) (hpow 2)
  · exact LowQuotient.abs_div_bound hC (by simpa only [abs_neg] using hW)
      (pow_pos hc 3) (hpow 3)
  · intro i
    rw [capChartSigma_partial hF hp hVp i]
    have hfirst :
        |-coordPartial i (coordPartial 1 (coordPartial 1 (capFlowHeight Y))) p /
          (coordPartial 1 (capFlowHeight Y) p)^3| ≤ C / c^3 :=
      LowQuotient.abs_div_bound hC (by simpa only [abs_neg] using hWi i)
        (pow_pos hc 3) (hpow 3)
    have hnum : |3 * coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p *
        coordPartial i (coordPartial 1 (capFlowHeight Y)) p| ≤ 3 * C^2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
      calc
        _ = 3 * (|coordPartial 1 (coordPartial 1 (capFlowHeight Y)) p| *
            |coordPartial i (coordPartial 1 (capFlowHeight Y)) p|) := by ring
        _ ≤ 3 * (C * C) := mul_le_mul_of_nonneg_left
          (mul_le_mul hW (hVi i) (abs_nonneg _) hC) (by norm_num)
        _ = 3 * C^2 := by ring
    have hsecond := LowQuotient.abs_div_bound (by positivity) hnum (pow_pos hc 4) (hpow 4)
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
variable (hM : 0 ≤ M)
variable (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
variable (hq1 : ∀ i : Fin 2, ∀ p ∈ modelSquare, |coordPartial i q p| ≤ M)
variable (hq2 : ∀ i j : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j q) p| ≤ M)
variable (hq3 : ∀ i j k : Fin 2, ∀ p ∈ modelSquare, |coordPartial i (coordPartial j (coordPartial k q)) p| ≤ M)
include hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3

theorem capReciprocal_bounds_from_q {p : Coord} (hp : p ∈ capChartDomain) :
    0 < capChartRho Y p ∧ |capChartRho Y p| ≤ 1 / Real.exp (-2 * M) ∧
    (∀ i : Fin 2, |coordPartial i (capChartRho Y) p| ≤ flowCoordinateBound M / (Real.exp (-2 * M))^2) ∧
    |capChartSigma Y p| ≤ flowCoordinateBound M / (Real.exp (-2 * M))^3 ∧
    (∀ i : Fin 2, |coordPartial i (capChartSigma Y) p| ≤
      flowCoordinateBound M / (Real.exp (-2 * M))^3 +
        3 * (flowCoordinateBound M)^2 / (Real.exp (-2 * M))^4) := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hVlower (x : Coord) (hx : x ∈ capChartDomain) :
      Real.exp (-2 * M) ≤ coordPartial 1 (capFlowHeight Y) x := by
    rw [capFlowHeight_partial_one_eq hs hx]
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM (hq1 1) hx.2 hx.1).1
  exact capReciprocal_bounds_of_jets (capFlowHeight_contDiffOn hs) (flowCoordinateBound_nonneg hM)
    (Real.exp_pos _) (capFlowHeight_coordinate_bound hq hU hSU hY hrange hstart hode hM hq0 hq1 hq2 hq3)
    hVlower hp

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedIntegralEstimate
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem integrated_directed_energy_with_explicit_costs
    {A B C chi I u f : Coord → ℝ} {U : Set Coord} {tl tr sb st : ℝ}
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U)
    (hchi : ContDiffOn ℝ ∞ chi U) (hI : ContDiffOn ℝ ∞ I U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    (hchiSides : ∀ s ∈ Icc sb st, chi (boxPoint tl s) = 0 ∧ chi (boxPoint tr s) = 0)
    (hchiBottom : ∀ t ∈ Icc tl tr, chi (boxPoint t sb) = 0)
    (hEq : ∀ p ∈ U, multiplierOperator A B C u p = f p)
    (hchin : ∀ p ∈ closedRectangle tl tr sb st, 0 ≤ chi p)
    (lambda epsilon R c : ℝ) (hc : 0 < c) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hR : ∀ p ∈ closedRectangle tl tr sb st, |p 0| ≤ R) :
    (c / 2) * rectangleIntegral tl tr sb st (directedGradientEnergy chi I u st lambda) ≤
      ((1 + R^2) / (2 * c)) * rectangleIntegral tl tr sb st (directedForcingEnergy chi I f st lambda) +
      rectangleIntegral tl tr sb st (fun p => |directedCutoffError A chi I u st lambda epsilon p|) +
      rectangleIntegral tl tr sb st (directedCoercivityDefect A B C chi I u st lambda epsilon c) := by
  let m := directedM st lambda I
  let n := directedN st lambda epsilon I
  let Q := multiplierQuadratic A B C m n u
  let E := directedGradientEnergy chi I u st lambda
  let F := directedForcingEnergy chi I f st lambda
  let Err := directedCutoffError A chi I u st lambda epsilon
  let Def := directedCoercivityDefect A B C chi I u st lambda epsilon c
  let Source := fun p => f p * multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p
  have hW := directedWeight_contDiffOn st lambda hI
  have hm : ContDiffOn ℝ ∞ m U := hW.neg
  have hn : ContDiffOn ℝ ∞ n U :=
    (contDiffOn_const.mul (contDiffOn_apply ℝ ℝ 0 U)).mul hW
  have hcm := hchi.mul hm
  have hcn := hchi.mul hn
  have hut := partial_contDiffOn hu hU 0
  have hus := partial_contDiffOn hu hU 1
  have hgrad := (hut.pow 2).add (hus.pow 2)
  have hf : ContDiffOn ℝ ∞ f U :=
    (ellipticOperator_contDiffOn hU hA hB hC hu).congr (fun p hp => (hEq p hp).symm)
  have hEc : ContinuousOn E (closedRectangle tl tr sb st) :=
    (((hchi.mul hW).mul hgrad).continuousOn.mono hbox)
  have hFc : ContinuousOn F (closedRectangle tl tr sb st) :=
    (((hchi.mul hW).mul (hf.pow 2)).continuousOn.mono hbox)
  have hQ := multiplierQuadratic_contDiffOn hU hA hB hC hm hn hu
  have hchiQ : ContinuousOn (fun p => chi p * Q p) (closedRectangle tl tr sb st) :=
    (hchi.mul hQ).continuousOn.mono hbox
  have hErr := multiplierCutoffError_contDiffOn hU hA hchi hm hn hu
  have hErrc : ContinuousOn Err (closedRectangle tl tr sb st) := hErr.continuousOn.mono hbox
  have hDef : ContinuousOn Def (closedRectangle tl tr sb st) :=
    (hchi.continuousOn.mul ((continuousOn_const (c := (0 : ℝ))).sup
      ((((contDiffOn_const (c := c)).mul hW).mul hgrad).sub hQ).continuousOn)).mono hbox
  have htest : ContDiffOn ℝ ∞ (multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u) U :=
    (hcm.mul hus).add (hcn.mul hut)
  have hSource : ContinuousOn Source (closedRectangle tl tr sb st) := (hf.mul htest).continuousOn.mono hbox
  have hsplit : rectangleIntegral tl tr sb st Source =
      rectangleIntegral tl tr sb st (fun p => chi p * Q p) - rectangleIntegral tl tr sb st Err := by
    calc
      _ = rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p *
          multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        change f p * multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p =
          multiplierOperator A B C u p *
            multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p
        rw [hEq p (hbox hp)]
      _ = rectangleIntegral tl tr sb st
          (multiplierQuadratic A B C (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u) :=
        integrated_cutoff_directed_identity ht hs hU hA hB hC hchi hI hu hbox hchiSides hchiBottom lambda epsilon
      _ = rectangleIntegral tl tr sb st (fun p => chi p * Q p - Err p) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        exact multiplierQuadratic_cutoff_split hU hA hchi hm hn hu (hbox hp)
      _ = _ := rectangleIntegral_sub ht hs hchiQ hErrc
  have hdom := rectangleIntegral_mono ht hs (continuousOn_const.mul hEc) (hchiQ.add hDef)
    (fun p hp => directedCoercivityDefect_domination A B C chi I u st lambda epsilon c p (hchin p hp))
  change rectangleIntegral tl tr sb st (fun p => c * E p) ≤
    rectangleIntegral tl tr sb st (fun p => chi p * Q p + Def p) at hdom
  rw [rectangleIntegral_const_mul, rectangleIntegral_add ht hs hchiQ hDef] at hdom
  have hsourceBound (p : Coord) (hp : p ∈ closedRectangle tl tr sb st) :
      Source p ≤ (c / 2) * E p + ((1 + R^2) / (2 * c)) * F p := by
    have hWn : 0 ≤ directedWeight st lambda I p :=
      mul_nonneg (pow_nonneg (sub_nonneg.mpr hp.2.2) 8) (Real.exp_pos _).le
    have hpoint := directed_source_young_scalar (mul_nonneg (hchin p hp) hWn) hc heps heps1 (hR p hp)
      (f := f p) (ut := coordPartial 0 u p) (us := coordPartial 1 u p)
    have hfac := cutoff_test_factor chi I u st lambda epsilon p
    dsimp [Source]
    rw [hfac]
    exact (le_abs_self _).trans (by
      convert hpoint using 1
      all_goals try with_reducible_and_instances rfl
      dsimp [E, F, directedGradientEnergy, directedForcingEnergy]
      ring)
  have hsourceIntegral := rectangleIntegral_mono ht hs hSource
    ((continuousOn_const.mul hEc).add (continuousOn_const.mul hFc)) hsourceBound
  change rectangleIntegral tl tr sb st Source ≤ rectangleIntegral tl tr sb st
    (fun p => (c / 2) * E p + ((1 + R^2) / (2 * c)) * F p) at hsourceIntegral
  have hcE : ContinuousOn (fun p => (c / 2) * E p) (closedRectangle tl tr sb st) :=
    continuousOn_const.mul hEc
  have hcF : ContinuousOn (fun p => ((1 + R^2) / (2 * c)) * F p) (closedRectangle tl tr sb st) :=
    continuousOn_const.mul hFc
  rw [rectangleIntegral_add ht hs hcE hcF,
    rectangleIntegral_const_mul, rectangleIntegral_const_mul] at hsourceIntegral
  have herrorIntegral := rectangleIntegral_mono ht hs hErrc hErrc.abs (fun p hp => le_abs_self (Err p))
  change (c / 2) * rectangleIntegral tl tr sb st E ≤
    ((1 + R^2) / (2 * c)) * rectangleIntegral tl tr sb st F +
    rectangleIntegral tl tr sb st (fun p => |Err p|) + rectangleIntegral tl tr sb st Def
  nlinarith only [hdom, hsplit, hsourceIntegral, herrorIntegral]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_IntegratedCapOverlap
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem actual_cap_integrated_overlap_estimate
    {g0 eta : MetricField} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    {L R A0 b kappa c1 c2 glow lambda epsilon MI M MK : ℝ}
    {G1 B C I u f : Coord → ℝ}
    (hL : -2 < L) (hR : R < 2) (hA0 : -2 < A0) (hAb : A0 ≤ b) (hb : b ≤ 0)
    (hk : 0 < kappa) (hc1 : 0 < c1) (hc2 : 0 < c2) (hg : 0 < glow)
    (hM : 0 ≤ M) (hMK : 0 ≤ MK) (hlambda : 0 ≤ lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hK : ContDiffOn ℝ ∞ (capPullback Y (gaussianCurvature (g0+eta))) capChartDomain)
    (hG1 : ContDiffOn ℝ ∞ G1 capChartDomain) (hB : ContDiffOn ℝ ∞ B capChartDomain)
    (hC : ContDiffOn ℝ ∞ C capChartDomain) (hI : ContDiffOn ℝ ∞ I capChartDomain)
    (hu : ContDiffOn ℝ ∞ u capChartDomain)
    (hEq : ∀ p ∈ capChartDomain,
      multiplierOperator (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C u p = f p)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox)
    (himage : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      capChart Y p ∈ U)
    (hdisp : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50)
    (hIv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |I p| ≤ MI)
    (hIi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hGlow : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, glow ≤ G1 p)
    (hAv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      |G1 p*capPullback Y (gaussianCurvature (g0+eta)) p| ≤ M)
    (hAi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) p| ≤ M)
    (hBv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |B p| ≤ M)
    (hCv : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b, |C p| ≤ M)
    (hKi : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      ∀ i : Fin 2, |coordPartial i (capPullback Y (gaussianCurvature (g0+eta))) p| ≤ MK)
    (hcoercive : ∀ p ∈ closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b,
      capPullback Y (gaussianCurvature (g0+eta)) p ≤ c1*edgeDistance b p →
      c2*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
        multiplierQuadratic (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C
          (directedM b lambda I) (directedN b lambda epsilon I) u p) :
    let D := capDistanceBound A0 b
    let COverlap := capOverlapEnergyCost L R A0 b kappa c1 c2 glow M lambda MI
    let HElliptic := capEllipticRatioBudget L R A0 b kappa c1 glow MK M
    (c2/2)*rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b
      (directedGradientEnergy (capSpatialCutoff L R A0) I u b lambda) ≤
      ((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6)*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b (fun p => (f p)^2) +
      (COverlap*(D^6+HElliptic))*
        rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom A0) b (fun p => (u p)^2) := by
  let tl := capOuterLeft L
  let tr := capOuterRight R
  let sb := capOuterBottom A0
  let D := capDistanceBound A0 b
  let c := capOverlapThreshold kappa c1 D
  let A := fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q
  let K := capPullback Y (gaussianCurvature (g0+eta))
  let chi := capSpatialCutoff L R A0
  let chi2 := capOuterSpatialCutoff L R A0
  let v := ellipticWeightC1 b c chi2 K
  let E := ellipticEnergy A v u
  let Err := directedCutoffError A chi I u b lambda epsilon
  let Def := directedCoercivityDefect A B C chi I u b lambda epsilon c2
  let COverlap := capOverlapEnergyCost L R A0 b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R A0 b kappa c1 glow MK M
  obtain ⟨htlo,htwidth,htone,hrone,hrwidth,htrhi,hsblo,hswidth,hsone,hlt,hrt⟩ :=
    capOuterRectangle_edges hL hR hA0
  have ht : tl ≤ tr := by dsimp only [tl,tr] <;> linarith
  have hs : sb ≤ b := by dsimp only [sb] <;> linarith
  have hD : 0 ≤ D := sub_nonneg.mpr hs
  have hc : 0 < c := capOverlapThreshold_pos hk hc1 hD
  have hbox : closedRectangle tl tr sb b ⊆ capChartDomain :=
    capOuterRectangle_subset_domain hL hR hA0 (by linarith)
  have hA : ContDiffOn ℝ ∞ A capChartDomain := hG1.mul hK
  have hchi : ContDiffOn ℝ ∞ chi capChartDomain := (capSpatialCutoff_contDiff _ _ _).contDiffOn
  have hchi2 : ContDiffOn ℝ ∞ chi2 capChartDomain := (capOuterSpatialCutoff_contDiff _ _ _).contDiffOn
  have hv : ContDiffOn ℝ 1 v capChartDomain := ellipticWeightC1_contDiffOn hc
    (hchi2.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hK.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hW := directedWeight_contDiffOn b lambda hI
  have hm := hW.neg
  have hn : ContDiffOn ℝ ∞ (directedN b lambda epsilon I) capChartDomain :=
    (contDiffOn_const.mul (contDiffOn_apply ℝ ℝ 0 _)).mul hW
  have hut := partial_contDiffOn hu capChartDomain_isOpen 0
  have hus := partial_contDiffOn hu capChartDomain_isOpen 1
  have hgrad := (hut.pow 2).add (hus.pow 2)
  have hQ := multiplierQuadratic_contDiffOn capChartDomain_isOpen hA hB hC hm hn hu
  have hErr : ContinuousOn Err (closedRectangle tl tr sb b) :=
    (multiplierCutoffError_contDiffOn capChartDomain_isOpen hA hchi hm hn hu).continuousOn.mono hbox
  have hDef : ContinuousOn Def (closedRectangle tl tr sb b) :=
    (hchi.continuousOn.mul ((continuousOn_const (c := (0 : ℝ))).sup
      ((((contDiffOn_const (c := c2)).mul hW).mul hgrad).sub hQ).continuousOn)).mono hbox
  obtain ⟨_,_,hEnergy,_⟩ := elliptic_fields_C1 capChartDomain_isOpen hA hB hC hv hu
  have hE : ContinuousOn E (closedRectangle tl tr sb b) := hEnergy.mono hbox
  have hX : 0 ≤ capSpatialDerivativeConstant L R A0 :=
    (abs_nonneg _).trans (capSpatialCutoff_partial_uniform hL hR hA0 (boxPoint 0 0) 0)
  have hconst := directedCostConstants_nonneg (S := 2) (MI := MI) hD hM hlambda hX hc2.le
  have hOverlap : 0 ≤ COverlap := by
    dsimp only [COverlap,capOverlapEnergyCost]
    exact mul_nonneg (add_nonneg hconst.1 hconst.2) (by positivity)
  have hpoint (p : Coord) (hp : p ∈ closedRectangle tl tr sb b) : |Err p|+Def p ≤ COverlap*E p := by
    have hpD := hbox hp
    exact actual_cap_directed_costs_le_elliptic hL hR hA0 hk hc1 hc2.le hg hD hM hlambda heps heps1
      hbackground hsupport (himage p hp) (hdisp p hp) hp.2.2
      (by dsimp only [edgeDistance,D,capDistanceBound] <;> linarith [hp.2.1])
      (abs_lt.mpr hpD.1).le (abs_lt.mpr hpD.2).le (hIv p hp)
      ((hI.contDiffAt (capChartDomain_isOpen.mem_nhds hpD)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hIi p hp)
      (hGlow p hp) ((hA.contDiffAt (capChartDomain_isOpen.mem_nhds hpD)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hAv p hp) (hAi p hp) (hBv p hp) (hCv p hp) (hcoercive p hp)
  have hcostIntegral := rectangleIntegral_mono ht hs (hErr.abs.add hDef) (continuousOn_const.mul hE) hpoint
  change rectangleIntegral tl tr sb b (fun p => |Err p| + Def p) ≤
    rectangleIntegral tl tr sb b (fun p => COverlap * E p) at hcostIntegral
  rw [rectangleIntegral_add ht hs hErr.abs hDef, rectangleIntegral_const_mul] at hcostIntegral
  have hEllRaw := threeEdge_elliptic_energy_bound htwidth hrwidth hswidth ht hs hc hMK hg hM
    capChartDomain_isOpen hK hG1 hB hC hu hbox hEq hKi hGlow hAv (fun p hp => hAi p hp 1) hBv hCv
  have hEll : rectangleIntegral tl tr sb b E ≤
      D^6*rectangleIntegral tl tr sb b (fun p => (f p)^2) +
        (D^6+HElliptic)*rectangleIntegral tl tr sb b (fun p => (u p)^2) := by
    calc
      _ = rectangleIntegral tl tr sb b
          (ellipticEnergy A (ellipticWeight b c
            (threeEdgeCutoff (capOuterLeft L) (capOuterLeftOne L) (capOuterRightOne R)
              (capOuterRight R) (capOuterBottom A0) (capOuterBottomOne A0)) K) u) := by
        apply rectangleIntegral_congr ht hs
        intro p hp
        change ellipticWeightC1 b c chi2 K p * _ = _
        rw [ellipticWeightC1_eq hp.2.2]
        change ellipticWeight b c (capOuterSpatialCutoff L R A0) K p * _ = _
        rw [capOuterSpatialCutoff_eq_threeEdge]
        rfl
      _ ≤ _ := hEllRaw
  have hf : ContDiffOn ℝ ∞ f capChartDomain :=
    (ellipticOperator_contDiffOn capChartDomain_isOpen hA hB hC hu).congr (fun p hp => (hEq p hp).symm)
  have hF : ContinuousOn (directedForcingEnergy chi I f b lambda) (closedRectangle tl tr sb b) :=
    (((hchi.mul hW).mul (hf.pow 2)).continuousOn.mono hbox)
  have hf2 : ContinuousOn (fun p => (f p)^2) (closedRectangle tl tr sb b) := (hf.pow 2).continuousOn.mono hbox
  have hforcing := rectangleIntegral_mono ht hs hF (continuousOn_const.mul hf2)
    (fun p hp => directedForcingEnergy_bound hlambda (sub_nonneg.mpr hp.2.2)
      (show edgeDistance b p ≤ D by dsimp only [edgeDistance,D,capDistanceBound] <;> linarith [hp.2.1])
      (abs_lt.mpr (hbox hp).2).le (hIv p hp) (capSpatialCutoff_range L R A0 p))
  change rectangleIntegral tl tr sb b (directedForcingEnergy chi I f b lambda) ≤
    rectangleIntegral tl tr sb b (fun p => (D^8*Real.exp (lambda*2+MI)) * (f p)^2) at hforcing
  rw [rectangleIntegral_const_mul] at hforcing
  obtain ⟨hsides,hbottom⟩ := capSpatialCutoff_outer_boundary (b := b) hL hR hA0
  have hdir := integrated_directed_energy_with_explicit_costs ht hs capChartDomain_isOpen hA hB hC
    hchi hI hu hbox hsides hbottom hEq (fun p _ => (capSpatialCutoff_range L R A0 p).1)
      lambda epsilon 2 c2 hc2 heps heps1 (fun p hp => (abs_lt.mpr (hbox hp).1).le)
  norm_num only [show (1 : ℝ)+2^2=5 by norm_num] at hdir
  have hsourceConstant : 0 ≤ (5 : ℝ)/(2*c2) := by positivity
  have hcombined := add_le_add (mul_le_mul_of_nonneg_left hforcing hsourceConstant)
    (hcostIntegral.trans (mul_le_mul_of_nonneg_left hEll hOverlap))
  change (c2/2)*rectangleIntegral tl tr sb b (directedGradientEnergy chi I u b lambda) ≤ _
  exact hdir.trans (by
    convert hcombined using 1 <;> (first | rfl | ring))

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowHeightCoefficients
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def heightChartA (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) : Coord → ℝ :=
  capTransportA Y (heightOriginalA g z)

def heightChartB (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (ell : ℕ) : Coord → ℝ :=
  capPullback Y (heightOriginalB g z ell)

def heightChartC (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (ell : ℕ) : Coord → ℝ :=
  capTransportC Y (heightOriginalA g z) (heightOriginalC0 g z ell)

def heightChartG1 (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ :=
  capPullback Y (darbouxG g z) p * (capChartRho Y p) ^ 2

def heightChartRemainder (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ)
    (ell : ℕ) (p : Coord) : ℝ :=
  (capPullback Y (curvatureDriftError g z) p - capPullback Y (coordPartial 1 (darbouxG g z)) p) /
      (capPullback Y (darbouxG g z) p * capChartRho Y p) -
    (2 * (ell : ℝ) + 1) * capChartSigma Y p / (capChartRho Y p) ^ 2

variable {g : MetricField} {z u : Coord → ℝ} {U : Set Coord} {p : Coord} {Y : ℝ → ℝ → ℝ}

theorem heightOriginalA_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) :
    ContDiffOn ℝ ∞ (heightOriginalA g z) U :=
  (gaussianCurvature_contDiffOn hg hU).mul (darbouxG_contDiffOn hg hU hz hyy)

theorem heightOriginalA_partial_y (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U) :
    coordPartial 1 (heightOriginalA g z) p =
      coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
        gaussianCurvature g p * coordPartial 1 (darbouxG g z) p := by
  exact HessianCalculus.coordPartial_mul_at
    (((gaussianCurvature_contDiffOn hg hU).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (((darbouxG_contDiffOn hg hU hz hyy).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) 1

theorem heightOriginalC0_eq (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U) (ell : ℕ) :
    heightOriginalC0 g z ell p =
      coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
        gaussianCurvature g p * curvatureDriftError g z p +
        (ell : ℝ) * (coordPartial 1 (gaussianCurvature g) p * darbouxG g z p +
          gaussianCurvature g p * coordPartial 1 (darbouxG g z) p) := by
  unfold heightOriginalC0
  rw [geometric_quotient_drift hg hU hz hD hp (hyy p hp), heightOriginalA_partial_y hg hU hz hyy hp]

theorem heightChartA_eq (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord) :
    heightChartA g z Y p = heightChartG1 g z Y p * capPullback Y (gaussianCurvature g) p := by
  unfold heightChartA heightChartG1 capTransportA capPullback heightOriginalA
  ring

theorem heightChartA_partial_initial
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) :
    coordPartial 1 (heightChartA g z Y) p =
      darbouxG g z (capChart Y p) * capChartRho Y p * coordPartial 1 (gaussianCurvature g) (capChart Y p) +
        gaussianCurvature g (capChart Y p) *
          (capChartRho Y p * coordPartial 1 (darbouxG g z) (capChart Y p) +
            2 * darbouxG g z (capChart Y p) * capChartSigma Y p) := by
  rw [heightChartA, capTransportA_partial_initial hY hvar
    (heightOriginalA_contDiffOn hg hU hz hyy) hU hmap hp]
  unfold capPullback
  rw [heightOriginalA_partial_y hg hU hz hyy (hmap hp)]
  unfold heightOriginalA
  ring

theorem heightChartC_expanded
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) (ell : ℕ) :
    heightChartC g z Y ell p =
      gaussianCurvature g (capChart Y p) * darbouxG g z (capChart Y p) * capChartSigma Y p +
        capChartRho Y p *
          (coordPartial 1 (gaussianCurvature g) (capChart Y p) * darbouxG g z (capChart Y p) +
            gaussianCurvature g (capChart Y p) * curvatureDriftError g z (capChart Y p) +
            (ell : ℝ) * (coordPartial 1 (gaussianCurvature g) (capChart Y p) * darbouxG g z (capChart Y p) +
              gaussianCurvature g (capChart Y p) * coordPartial 1 (darbouxG g z) (capChart Y p))) := by
  unfold heightChartC capTransportC capPullback heightOriginalA
  rw [heightOriginalC0_eq hg hU hz hD hyy (hmap hp) ell]
  ring

theorem heightChartC_factor
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hp : p ∈ capChartDomain) (ell : ℕ) :
    heightChartC g z Y ell p = ((ell : ℝ) + 1) * coordPartial 1 (heightChartA g z Y) p +
      heightChartA g z Y p * heightChartRemainder g z Y ell p := by
  have hGne := (darbouxG_pos g z (capChart Y p) (hE _ (hmap hp)) (hyy _ (hmap hp))).ne'
  have hrhone := (capChartRho_pos hY hvar hp).ne'
  rw [heightChartC_expanded hg hU hz hD hyy hmap hp ell,
    heightChartA_partial_initial hg hU hz hyy hY hvar hmap hp]
  unfold heightChartA capTransportA heightOriginalA heightChartRemainder capPullback
  rw [SmoothLocal.DriftAlgebra.transverse_coefficient_polynomial,
    SmoothLocal.DriftAlgebra.transverse_coefficient_factor _ _ _ _ _ _ _ hGne hrhone]

theorem heightChartRemainder_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightChartRemainder g z Y ell) capChartDomain := by
  have hG := darbouxG_contDiffOn hg hU hz hyy
  have hPG := capPullback_contDiffOn hY hG hmap
  have hPGy := capPullback_contDiffOn hY (partial_contDiffOn hG hU 1) hmap
  have hPR := capPullback_contDiffOn hY (curvatureDriftError_contDiffOn hg hU hz hyy) hmap
  have hrho := capChartRho_contDiffOn hY hvar
  have hsigma := capChartSigma_contDiffOn hY hvar
  exact ((hPR.sub hPGy).div (hPG.mul hrho) (fun _ hp =>
    mul_ne_zero (darbouxG_pos g z _ (hE _ (hmap hp)) (hyy _ (hmap hp))).ne'
      (capChartRho_pos hY hvar hp).ne')).sub
    ((contDiffOn_const.mul hsigma).div (hrho.pow 2)
      (fun _ hp => pow_ne_zero 2 (capChartRho_pos hY hvar hp).ne'))

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_DriftOperatorIdentity
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Geometry.HessianCalculus

variable {q u a : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem coordinateDrift_twice_expanded
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U)
    (hU : IsOpen U) (hp : p ∈ U) :
    coordinateDrift q (coordinateDrift q u) p =
      coordPartial 0 (coordPartial 0 u) p -
        2 * q p * coordPartial 0 (coordPartial 1 u) p +
        (q p)^2 * coordPartial 1 (coordPartial 1 u) p -
        coordinateDrift q q p * coordPartial 1 u p := by
  have hqd : DifferentiableAt ℝ q p :=
    (hq.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hud (i : Fin 2) : DifferentiableAt ℝ (coordPartial i u) p :=
    ((partial_contDiffOn hu hU i).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hprod : DifferentiableAt ℝ (fun r => q r * coordPartial 1 u r) p := hqd.mul (hud 1)
  have hd (i : Fin 2) : coordPartial i (coordinateDrift q u) p =
      coordPartial i (coordPartial 0 u) p -
        (coordPartial i q p * coordPartial 1 u p + q p * coordPartial i (coordPartial 1 u) p) := by
    change coordPartial i (fun r => coordPartial 0 u r - q r * coordPartial 1 u r) p = _
    rw [coordPartial_sub_at (hud 0) hprod i, coordPartial_mul_at hqd (hud 1) i]
  change coordPartial 0 (coordinateDrift q u) p - q p * coordPartial 1 (coordinateDrift q u) p = _
  rw [hd 0, hd 1, coordPartial_comm hu hU hp 1 0]
  unfold coordinateDrift
  ring

theorem driftOperator_linearized_identity
    (hq : ContDiffOn ℝ ∞ q U) (hu : ContDiffOn ℝ ∞ u U)
    (ha : ContDiffOn ℝ ∞ a U) (hU : IsOpen U) (hp : p ∈ U)
    (Px Py : Coord → ℝ) (ell : ℕ) :
    driftOperator q a
      (fun r => -Px r - 2 * (ell : ℝ) * coordPartial 1 q r)
      (fun r => coordinateDrift q q r - Px r * q r - Py r +
        (ell : ℝ) * coordPartial 1 a r) u p =
      coordPartial 0 (coordPartial 0 u) p -
        2 * q p * coordPartial 0 (coordPartial 1 u) p +
        ((q p)^2 + a p) * coordPartial 1 (coordPartial 1 u) p -
        Px p * coordPartial 0 u p - Py p * coordPartial 1 u p -
        (ell : ℝ) * (2 * coordPartial 1 q p * coordPartial 0 u p -
          coordPartial 1 (fun r => (q r)^2 + a r) p * coordPartial 1 u p) := by
  have hqd : DifferentiableAt ℝ q p :=
    (hq.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have had : DifferentiableAt ℝ a p :=
    (ha.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hqq : DifferentiableAt ℝ (fun r => q r * q r) p := hqd.mul hqd
  have htotal : coordPartial 1 (fun r => (q r)^2 + a r) p =
      2 * q p * coordPartial 1 q p + coordPartial 1 a p := by
    simp only [pow_two]
    rw [coordPartial_add_at hqq had 1, coordPartial_mul_at hqd hqd 1]
    ring
  unfold driftOperator
  rw [coordinateDrift_twice_expanded hq hu hU hp, htotal]
  unfold coordinateDrift
  ring

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_HeightCoefficientRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem height_jetEnergy_first_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p)) U := by
  have h0 := partial_contDiffOn hz hU 0
  have h1 := partial_contDiffOn hz hU 1
  fin_cases i
  · have hf : ContDiffOn ℝ ∞ (fun p => -2 * g p 1 1 * coordPartial 0 z p +
        (g p 0 1 + g p 1 0) * coordPartial 1 z p) U :=
      ((contDiffOn_const.mul (hg.1 1 1)).mul h0).add (((hg.1 0 1).add (hg.1 1 0)).mul h1)
    apply hf.congr
    intro p _
    simpa only [Fin.mk_zero, ↓reduceIte] using
      coordPartial_jetEnergy g p (fun r => coordPartial r z p) 0
  · have hf : ContDiffOn ℝ ∞ (fun p => (g p 0 1 + g p 1 0) * coordPartial 0 z p -
        2 * g p 0 0 * coordPartial 1 z p) U :=
      (((hg.1 0 1).add (hg.1 1 0)).mul h0).sub ((contDiffOn_const.mul (hg.1 0 0)).mul h1)
    apply hf.congr
    intro p _
    simpa only [Fin.mk_one, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using
      coordPartial_jetEnergy g p (fun r => coordPartial r z p) 1

theorem height_christoffelAlongD_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => christoffelAlongD g p (hessianQuotient g z p) i) U := by
  have hq := hessianQuotient_contDiffOn hg hU hz hyy
  have hf : ContDiffOn ℝ ∞ (fun p => christoffel g i 0 0 p -
      2 * hessianQuotient g z p * christoffel g i 0 1 p +
      (hessianQuotient g z p)^2 * christoffel g i 1 1 p) U :=
    ((christoffel_contDiffOn hg hU i 0 0).sub
      ((contDiffOn_const.mul hq).mul (christoffel_contDiffOn hg hU i 0 1))).add
      ((hq.pow 2).mul (christoffel_contDiffOn hg hU i 1 1))
  exact hf.congr (fun p hp => christoffelAlongD_eq hg hU hp _ i)

theorem heightPFirst_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    ContDiffOn ℝ ∞ (heightPFirst g z i) U := by
  have hh := covHessian_contDiffOn hg hU hz 1 1
  have hf : ContDiffOn ℝ ∞ (fun p => christoffelAlongD g p (hessianQuotient g z p) i +
      gaussianCurvature g p *
        (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
          heightEnergy g z p * christoffel g i 1 1 p / (covHessian g z p 1 1)^2)) U :=
    (height_christoffelAlongD_contDiffOn hg hU hz hyy i).add
      ((gaussianCurvature_contDiffOn hg hU).mul
        (((height_jetEnergy_first_contDiffOn hg hU hz i).div hh hyy).add
          (((heightEnergy_contDiffOn hg hU hz).mul (christoffel_contDiffOn hg hU i 1 1)).div
            (hh.pow 2) (fun p hp => pow_ne_zero 2 (hyy p hp)))))
  exact hf.congr (fun p hp => heightPFirst_eq hg hU hp (hyy p hp) i)

end SmoothLocal.Geometry

namespace SmoothLocal.Flow
open SmoothLocal.Geometry

theorem heightOriginalB_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightOriginalB g z ell) U :=
  (heightPFirst_contDiffOn hg hU hz hyy 0).neg.sub
    (contDiffOn_const.mul (partial_contDiffOn (hessianQuotient_contDiffOn hg hU hz hyy) hU 1))

theorem heightChartB_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hmap : MapsTo (capChart Y) capChartDomain U) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain :=
  capPullback_contDiffOn hY (heightOriginalB_contDiffOn hg hU hz hyy ell) hmap

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_ConstructedHeightFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem modelOpenSquare_isOpen : IsOpen modelOpenSquare := coordinateRectangle_isOpen _ _ _

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_CoordinateFirstBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.CoordinateBound

theorem mul_through_one {f h : Coord → ℝ} {U : Set Coord} {A B : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfB : CoordinateBound f U 1 A) (hhB : CoordinateBound h U 1 B) :
    CoordinateBound (fun x => f x * h x) U 1 (2 * A * B) := by
  intro ds hds p hp
  have hab (vs ws : List (Fin 2)) (hv : vs.length ≤ 1) (hw : ws.length ≤ 1) :
      |iteratedCoordPartial vs f p * iteratedCoordPartial ws h p| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul (hfB vs hv p hp) (hhB ws hw p hp) (abs_nonneg _) hA
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  cases ds with
  | nil => exact (hab [] [] (by norm_num) (by norm_num)).trans (by nlinarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.product_one hf hh hU hp i]
      exact ((abs_add_le _ _).trans
        (add_le_add (hab [i] [] (by norm_num) (by norm_num))
          (hab [] [i] (by norm_num) (by norm_num)))).trans (le_of_eq (by ring))
    | cons j ds => simp only [List.length_cons] at hds; omega

end SmoothLocal.Geometry.CoordinateBound

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_HeightFlowBoundTools
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capPullback_bound_one {u : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {A F : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hA : 0 ≤ A) (hF : 0 ≤ F)
    (huB : CoordinateBound u modelSquare 1 A)
    (hFB : CoordinateBound (capFlowHeight Y) capChartDomain 3 F) :
    CoordinateBound (capPullback Y u) capChartDomain 1 (A * (1 + F)) := by
  intro ds hds p hp
  have hv : |u (capChart Y p)| ≤ A := huB [] (by norm_num) _ (hmapS hp)
  have hdu (i : Fin 2) : |coordPartial i u (capChart Y p)| ≤ A := huB [i] (by norm_num) _ (hmapS hp)
  have hdf (i : Fin 2) : |coordPartial i (capFlowHeight Y) p| ≤ F := hFB [i] (by norm_num) p hp
  cases ds with
  | nil => exact hv.trans (by nlinarith [mul_nonneg hA hF])
  | cons i ds =>
    cases ds with
    | nil =>
      change |coordPartial i (capPullback Y u) p| ≤ A * (1 + F)
      rw [capPullback_partial hY hp ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) i]
      have h0 : |if i = 0 then coordPartial 0 u (capChart Y p) else 0| ≤ A := by
        split_ifs
        · exact hdu 0
        · simpa only [abs_zero] using hA
      have h1 : |coordPartial 1 u (capChart Y p) * coordPartial i (capFlowHeight Y) p| ≤ A * F := by
        rw [abs_mul]
        exact mul_le_mul (hdu 1) (hdf i) (abs_nonneg _) hA
      exact ((abs_add_le _ _).trans (add_le_add h0 h1)).trans (le_of_eq (by ring))
    | cons _ ds => simp only [List.length_cons] at hds; omega

theorem heightOriginalB_bound_one {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {P Q : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hne : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hPB : CoordinateBound (heightPFirst g z 0) modelSquare 1 P)
    (hqB : CoordinateBound (hessianQuotient g z) modelSquare 3 Q) (ell : ℕ) :
    CoordinateBound (heightOriginalB g z ell) modelSquare 1 (P + 2 * (ell : ℝ) * Q) := by
  have hI : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hP := heightPFirst_contDiffOn hg hU hz hne 0
  have hq := hessianQuotient_contDiffOn hg hU hz hne
  have hqy := partial_contDiffOn hq hU 1
  have hqyB : CoordinateBound (coordPartial 1 (hessianQuotient g z)) modelSquare 1 Q :=
    (hqB.mono (by norm_num : 2 ≤ 3) le_rfl).partial_bound 1
  have ht := CoordinateBound.const_mul (hqy.mono hI) isOpen_interior
    (hqyB.restrict_domain interior_subset) (2 * (ell : ℝ))
  have hb := CoordinateBound.sub (hP.neg.mono hI) (contDiffOn_const.mul (hqy.mono hI)) isOpen_interior
    (CoordinateBound.neg (hP.mono hI) isOpen_interior (hPB.restrict_domain interior_subset)) ht
  have hc : |2 * (ell : ℝ)| = 2 * (ell : ℝ) := abs_of_nonneg (by positivity)
  rw [hc] at hb
  exact CoordinateBound.of_modelSquare_interior (heightOriginalB_contDiffOn hg hU hz hne ell) hU hSU hb

theorem capChartRho_lower_from_q
    {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hM : 0 ≤ M) (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {p : Coord} (hp : p ∈ capChartDomain) : 1 / Real.exp (2 * M) ≤ capChartRho Y p := by
  have hs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hpos := cap_flow_initial_deriv_pos hq hU hSU hY hrange hstart hode hp.2 hp.1
  have hupper := (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hq1 hp.2 hp.1).2
  unfold capChartRho
  rw [capFlowHeight_partial_one_eq hs hp]
  apply (le_div_iff₀ hpos).mpr
  calc
    _ ≤ (1 / Real.exp (2 * M)) * Real.exp (2 * M) := mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = 1 := one_div_mul_cancel (Real.exp_ne_zero _)

theorem heightChartRemainder_bound_of_low_coefficients
    (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord) (ell : ℕ)
    {DE DG SG lowerG RL : ℝ} (hDE : 0 ≤ DE) (hDG : 0 ≤ DG) (hSG : 0 ≤ SG)
    (hGL : 0 < lowerG) (hRL : 0 < RL)
    (herror : |curvatureDriftError g z (capChart Y p)| ≤ DE)
    (hGy : |coordPartial 1 (darbouxG g z) (capChart Y p)| ≤ DG)
    (hG : lowerG ≤ darbouxG g z (capChart Y p))
    (hrho : RL ≤ capChartRho Y p) (hsigma : |capChartSigma Y p| ≤ SG) :
    |heightChartRemainder g z Y ell p| ≤
      (DE + DG) / (lowerG * RL) + (2 * (ell : ℝ) + 1) * SG / RL^2 := by
  have hGpos : 0 < darbouxG g z (capChart Y p) := hGL.trans_le hG
  have hrhopos : 0 < capChartRho Y p := hRL.trans_le hrho
  have hden : lowerG * RL ≤ |darbouxG g z (capChart Y p) * capChartRho Y p| := by
    rw [abs_of_pos (mul_pos hGpos hrhopos)]
    exact mul_le_mul hG hrho hRL.le hGpos.le
  have hden2 : RL^2 ≤ |(capChartRho Y p)^2| := by
    rw [abs_pow, abs_of_pos hrhopos]
    exact pow_le_pow_left₀ hRL.le hrho 2
  have hnum := (abs_sub _ _).trans (add_le_add herror hGy)
  have hfirst := LowQuotient.abs_div_bound (add_nonneg hDE hDG) hnum (mul_pos hGL hRL) hden
  have hnum2 : |(2 * (ell : ℝ) + 1) * capChartSigma Y p| ≤ (2 * (ell : ℝ) + 1) * SG := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (ell : ℝ) + 1)]
    exact mul_le_mul_of_nonneg_left hsigma (by positivity)
  have hsecond := LowQuotient.abs_div_bound (by positivity) hnum2 (pow_pos hRL 2) hden2
  exact (abs_sub _ _).trans (add_le_add hfirst hsecond)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_HeightPrincipalBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem capFlowHeight_partial_bound_of_rho
    {q : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {M : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hsmall : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hM : 0 ≤ M) (hrho : ∀ p ∈ capChartDomain, 1 / Real.exp (2 * M) ≤ capChartRho Y p)
    {p : Coord} (hp : p ∈ capChartDomain) (i : Fin 2) :
    |coordPartial i (capFlowHeight Y) p| ≤ flowCoordinateBound M := by
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one]
  · rw [capFlowHeight_partial_time hY hode hp, abs_neg]
    exact (hsmall _ (hmapS hp)).trans ((by norm_num : (1 : ℝ) / 100 ≤ 1).trans
      (flowCoordinateBound_dominates hM).2.1)
  · have hpos := capFlowHeight_partial_initial_pos hY hvar hp
    rw [abs_of_pos hpos]
    have hl : 1 / Real.exp (2 * M) ≤ 1 / coordPartial 1 (capFlowHeight Y) p := hrho p hp
    have hupper : coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2 * M) := by
      simpa only [one_mul] using (div_le_div_iff₀ (Real.exp_pos _) hpos).mp hl
    exact hupper.trans (flowCoordinateBound_dominates hM).2.2.1

theorem capPullback_bound_one_from_partials
    {u : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {A F : ℝ}
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hA : 0 ≤ A) (hF : 0 ≤ F) (huB : CoordinateBound u modelSquare 1 A)
    (hFB : ∀ i : Fin 2, ∀ p ∈ capChartDomain, |coordPartial i (capFlowHeight Y) p| ≤ F) :
    CoordinateBound (capPullback Y u) capChartDomain 1 (A * (1 + F)) := by
  intro ds hds p hp
  cases ds with
  | nil => exact (huB [] (by norm_num) _ (hmapS hp)).trans (by nlinarith [mul_nonneg hA hF])
  | cons i ds =>
    cases ds with
    | nil =>
      change |coordPartial i (capPullback Y u) p| ≤ A * (1 + F)
      rw [capPullback_partial hY hp ((hu.contDiffAt (hU.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) i]
      have hdu (j : Fin 2) : |coordPartial j u (capChart Y p)| ≤ A := huB [j] (by norm_num) _ (hmapS hp)
      have h0 : |if i = 0 then coordPartial 0 u (capChart Y p) else 0| ≤ A := by
        split_ifs
        · exact hdu 0
        · simpa only [abs_zero] using hA
      have h1 : |coordPartial 1 u (capChart Y p) * coordPartial i (capFlowHeight Y) p| ≤ A * F := by
        rw [abs_mul]
        exact mul_le_mul (hdu 1) (hFB i p hp) (abs_nonneg _) hA
      exact ((abs_add_le _ _).trans (add_le_add h0 h1)).trans (le_of_eq (by ring))
    | cons j ds => simp only [List.length_cons] at hds; omega

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_PhysicalCapTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem cap_gradient_estimate_to_physical_images
    {Y : ℝ → ℝ → ℝ} {q u f : Coord → ℝ} {V : Set Coord}
    {e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2:ℝ) 2) t)
    (hsource : e.source = pairRectangle 2 (-2) 2)
    (heq : (e : (ℝ × ℝ) → (ℝ × ℝ)) = triangularFlow Y)
    (hu : ContDiffOn ℝ ∞ u V) (hV : IsOpen V)
    (hmap : MapsTo (capChart Y) capChartDomain V)
    {tl tr sb st TL TR SB ST M a b : ℝ}
    (ht : tl ≤ tr) (hs : sb ≤ st) (hT : TL ≤ TR) (hS : SB ≤ ST)
    (hbox : closedRectangle tl tr sb st ⊆ capChartDomain)
    (hBOX : closedRectangle TL TR SB ST ⊆ capChartDomain)
    (hq : ∀ p ∈ capChartDomain, |q (capChart Y p)| ≤ 1)
    (hJ : ∀ p ∈ capChartDomain,
      Real.exp (-2*M) ≤ coordPartial 1 (capFlowHeight Y) p ∧
        coordPartial 1 (capFlowHeight Y) p ≤ Real.exp (2*M))
    (hf : ContinuousOn f (capChart Y '' closedRectangle TL TR SB ST))
    (hestimate : rectangleIntegral tl tr sb st (coordinateGradientSquare (capPullback Y u)) ≤
      a*rectangleIntegral TL TR SB ST (fun p => (capPullback Y f p)^2)+
        b*rectangleIntegral TL TR SB ST (fun p => (capPullback Y u p)^2)) :
    (∫ p in capChart Y '' closedRectangle tl tr sb st, coordinateGradientSquare u p) ≤
      (Real.exp (2*M)*(2+3*(Real.exp (2*M))^2))*Real.exp (2*M)*(|a|+|b|+1)*
        ((∫ p in capChart Y '' closedRectangle TL TR SB ST, (f p)^2)+
          (∫ p in capChart Y '' closedRectangle TL TR SB ST, (u p)^2)) := by
  have huI : ContinuousOn u (capChart Y '' closedRectangle TL TR SB ST) :=
    hu.continuousOn.mono (by rintro _ ⟨p,hp,rfl⟩; exact hmap (hBOX hp))
  have hfc : ContinuousOn (capPullback Y f) (closedRectangle TL TR SB ST) :=
    hf.comp ((capChart_contDiffOn hYs).continuousOn.mono hBOX) (fun p hp => ⟨p,hp,rfl⟩)
  have huc : ContinuousOn (capPullback Y u) (closedRectangle TL TR SB ST) :=
    (capPullback_contDiffOn hYs hu hmap).continuousOn.mono hBOX
  have hF : 0 ≤ rectangleIntegral TL TR SB ST (fun p => (capPullback Y f p)^2) := by
    have he := rectangleIntegral_eq_coordinate_closed_area hT hS (hfc.pow 2)
    change rectangleIntegral TL TR SB ST (fun p => (capPullback Y f p)^2) = _ at he
    rw [he]
    exact integral_nonneg (fun p => sq_nonneg _)
  have hU : 0 ≤ rectangleIntegral TL TR SB ST (fun p => (capPullback Y u p)^2) := by
    have he := rectangleIntegral_eq_coordinate_closed_area hT hS (huc.pow 2)
    change rectangleIntegral TL TR SB ST (fun p => (capPullback Y u p)^2) = _ at he
    rw [he]
    exact integral_nonneg (fun p => sq_nonneg _)
  have hFarea := cap_pullback_square_integral_le_image hYs hvar hsource heq hT hS hBOX
    (fun p hp => hJ p (hBOX hp)) hf
  have hUarea := cap_pullback_square_integral_le_image hYs hvar hsource heq hT hS hBOX
    (fun p hp => hJ p (hBOX hp)) huI
  have hGrad := (cap_gradient_integral_bounds hYs hvar hode hsource heq hu hV hmap ht hs hbox
    (fun p hp => hq p (hbox hp)) (fun p hp => hJ p (hbox hp))).2
  exact scalar_two_integral_transport (Real.exp_pos _).le (by positivity) hF hU
    (integral_nonneg (fun p => sq_nonneg (f p))) (integral_nonneg (fun p => sq_nonneg (u p)))
    hFarea hUarea hestimate hGrad

end SmoothLocal.Flow

end

end OAI
end


