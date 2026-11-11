-- Prove2me | Definitions.Def_Q226II014
-- name    : Q226II014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:53:27.722783+00:00
-- url     : https://prove2.me/theorems/5446cfe8-2697-4cd2-b083-8e83fd201f63
-- title:
--   Definitions bundle Q226II014 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 91 declarations of OpenAI's Lean: 91 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Caps_AllOrderCapEstimate`, `IsometricImmersion_Caps_AllOrderPhysicalCap`, `IsometricImmersion_Caps_BoundedClassCapRadius`, `IsometricImmersion_Caps_CapInductionData`, `IsometricImmersion_Caps_FiniteCapInduction`, `IsometricImmersion_Caps_FiniteCapPointwise`, `IsometricImmersion_Comparison_ActualComparisonEquation`, `IsometricImmersion_Comparison_ActualComparisonTestCost`, `IsometricImmersion_Comparison_ComparisonCoefficientBounds`, `IsometricImmersion_Comparison_ComparisonCoefficientDerivative`, `IsometricImmersion_Comparison_ComparisonCoefficientSmooth`, `IsometricImmersion_Coordinates_ActualCentralShearMargins`, `IsometricImmersion_Coordinates_ActualPatchQRectangle`, `IsometricImmersion_Coordinates_ActualShearHyperbolicity`, `IsometricImmersion_Coordinates_BoundedClassSlabSmallness`, `IsometricImmersion_Darboux_QClosedStripMargins`, `IsometricImmersion_Darboux_QCoefficientTube`, `IsometricImmersion_Darboux_QEnergyApplication`, `IsometricImmersion_Darboux_QFirstSpatialBounds`, `IsometricImmersion_Darboux_QHighEquation`, `IsometricImmersion_Darboux_QLowActualBounds`, `IsometricImmersion_Darboux_QMetricDensityDecomposition`, `IsometricImmersion_Darboux_QMetricJetTransfer`, `IsometricImmersion_Darboux_QPositiveFloor`, `IsometricImmersion_Darboux_QPrincipal`, `IsometricImmersion_Darboux_QResidualActive`, `IsometricImmersion_Darboux_QResidualFactors`, `IsometricImmersion_Darboux_QResidualL2`, `IsometricImmersion_Darboux_QSegmentAveraging`, `IsometricImmersion_Darboux_QSpatialJets`, `IsometricImmersion_Darboux_QSpatialRestriction`, `IsometricImmersion_Darboux_SixVariableQ`, `IsometricImmersion_Energy_ActualRemainderL2`, `IsometricImmersion_Energy_LocalizedRemainderL2`, `IsometricImmersion_Energy_MixedDerivativeL2`, `IsometricImmersion_Estimates_ActualRemainderFactors`, `IsometricImmersion_Estimates_BoundedClassHyperbolicity`, `IsometricImmersion_Estimates_BoundedClassQFloor`, `IsometricImmersion_Estimates_RemainderAreaBudget`, `IsometricImmersion_Taylor_TaylorResidual`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II011` and `Q226II012` of this split.
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
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
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

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_AllOrderCapEstimate
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

theorem exists_C8_one_flow_all_high_cap_estimates
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hzB : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1:ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) :
    ∃ (V : Set Coord) (Y : ℝ → ℝ → ℝ),
      IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ (hessianQuotient (g0+eta) z) V ∧
      CoordinateBound (hessianQuotient (g0+eta) z) modelSquare 3 (heightQuotientJetBound G Z d c) ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContinuousOn (uncurry Y) (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2:ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, Y s t ∈ Icc (-3:ℝ) 3) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, |Y s t-s| ≤ (1:ℝ)/50) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50) ∧
      ∀ m : ℕ,
        let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
        let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
        let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
        let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
        0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
        (∀ p ∈ capChartDomain,
          multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
            (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
              capPullback Y (actualHighRemainder (g0+eta) z m) p) ∧
        ∀ L R bottom top b : ℝ,
          -2 < L → R < 2 → -2 < bottom → L ≤ R → bottom ≤ top → top < b → b ≤ 0 →
          rectangleIntegral L R bottom top
            (fun p => (coordPartial 0 (capPullback Y (verticalJet z (m+3))) p)^2+
              (coordPartial 1 (capPullback Y (verticalJet z (m+3))) p)^2) ≤
            heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
              (capPullback Y (verticalJet z (m+3)))
              (capPullback Y (actualHighRemainder (g0+eta) z m)) := by
  have hg4 (i j : Fin 2) : CoordinateBound (fun p => (g0+eta) p i j) modelSquare 4 G :=
    (coordinateBound_of_frechet_bounds (hg.1 i j) hU hSU (hgB i j)).mono (by norm_num) le_rfl
  have hz5 : CoordinateBound z modelSquare 5 Z := coordinateBound_five_of_frechet_eight hz hU hSU hzB
  obtain ⟨V,hV,hSV,hVU,_,hq,hqB⟩ :=
    exists_open_quotient_domain_with_closed_low_bounds hg hU hSU hz hG hZ hd hc hg4 hz5 hdet hyy
  obtain ⟨Y,hY,_,hstart,hode,_,hdisp50,hrange,_⟩ := exists_cap_flow hq hV hSV hsmall
  have hconf (s : ℝ) (hs : s ∈ Icc (-2:ℝ) 2) (t : ℝ) (ht : t ∈ Icc (-2:ℝ) 2) :
      Y s t ∈ Icc (-3:ℝ) 3 := abs_le.mp ((hrange s hs t ht).1.trans (by norm_num))
  have hYs := cap_flow_joint_contDiffOn hq hV hSV hY hconf hstart hode
  have hchart := capChart_contDiffOn hYs
  have hvar : ∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s :=
    fun s hs t ht => cap_flow_initial_deriv_pos hq hV hSV hY hconf hstart hode hs ht
  have hdisp (p : Coord) (hp : p ∈ capChartDomain) : |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50 :=
    hdisp50 (p 1) ⟨hp.2.1.le,hp.2.2.le⟩ (p 0) ⟨hp.1.1.le,hp.1.2.le⟩
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (g0+eta) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hyyO : ∀ p ∈ modelOpenSquare, covHessian (g0+eta) z p 1 1 ≠ 0 :=
    fun p hp => LowQuotient.denominator_ne_zero hc hyy p (modelOpenSquare_subset hp)
  have hPDE (m : ℕ) (p : Coord) (hp : p ∈ capChartDomain) :
      multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
        (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
          capPullback Y (actualHighRemainder (g0+eta) z m) p :=
    actual_flow_high_equation hgO modelOpenSquare_isOpen hzO
      (fun p hp => hD p (modelOpenSquare_subset hp)) hyyO hYs hode hvar hmapO m hp
  refine ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hconf,hdisp50,hdisp,?_⟩
  intro m
  obtain ⟨Ym,heps,heps1,hlambda,hc1,hc2,_,hstartm,hodem,hdispm,_,hestimatem⟩ :=
    exists_uniform_original_data_actual_high_cap_estimate hg hU hSU hz hG hZ hd hc he0 hg4 hz5
      hdet hyy hEfloor hsmall hD hk hbackground hsupport hcentral m
  have heq := capChart_eqOn_of_same_ode hq hV hSV hstart hode hdisp hstartm hodem hdispm
  refine ⟨heps,heps1,hlambda,hc1,hc2,hPDE m,?_⟩
  intro L R bottom top b hL hR hbottom hLR hbt htop hb
  have hT : closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b ⊆ capChartDomain :=
    capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hS : closedRectangle L R bottom top ⊆ capChartDomain := by
    intro p hp
    exact ⟨⟨hL.trans_le hp.1.1,hp.1.2.trans_lt hR⟩,
      ⟨hbottom.trans_le hp.2.1,by linarith [hp.2.2]⟩⟩
  obtain ⟨hlo,hli,hlu,hri,hrr,hro,hao,hai,hau,hlx,hrx⟩ := capOuterRectangle_edges hL hR hbottom
  have hOT : capOuterLeft L ≤ capOuterRight R := by linarith
  have hOS : capOuterBottom bottom ≤ b := by linarith
  have huint := capPullback_square_rectangle_eq_of_chart_eqOn heq (verticalJet z (m+3)) hOT hOS hT
  have hfint := capPullback_square_rectangle_eq_of_chart_eqOn heq (actualHighRemainder (g0+eta) z m) hOT hOS hT
  have hRHS : heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
      (capPullback Y (verticalJet z (m+3))) (capPullback Y (actualHighRemainder (g0+eta) z m)) =
      heightUniformCapEstimateRHS G Z d c e0 kappa (m+3) L R bottom top b
        (capPullback Ym (verticalJet z (m+3))) (capPullback Ym (actualHighRemainder (g0+eta) z m)) := by
    unfold heightUniformCapEstimateRHS
    rw [huint,hfint]
  rw [capPullback_gradient_rectangle_eq_of_chart_eqOn heq (verticalJet z (m+3)) hLR hbt hS,hRHS]
  exact hestimatem L R bottom top b hL hR hbottom hLR hbt htop hb

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_AllOrderPhysicalCap
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model SmoothLocal.HighEquation

theorem exists_C8_one_flow_physical_cap_estimates
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hzB : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1:ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) :
    ∃ (V : Set Coord) (Y : ℝ → ℝ → ℝ),
      IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ (hessianQuotient (g0+eta) z) V ∧
      CoordinateBound (hessianQuotient (g0+eta) z) modelSquare 3 (heightQuotientJetBound G Z d c) ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContinuousOn (uncurry Y) (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2:ℝ) 2, ∀ t ∈ Ioo (-2:ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2:ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, Y s t ∈ Icc (-3:ℝ) 3) ∧
      (∀ s ∈ Icc (-2:ℝ) 2, ∀ t ∈ Icc (-2:ℝ) 2, |Y s t-s| ≤ (1:ℝ)/50) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50) ∧
      (∀ tl tr sb st : ℝ, closedRectangle tl tr sb st ⊆ capChartDomain →
        IsCompact (capChart Y '' closedRectangle tl tr sb st) ∧
        MeasurableSet (capChart Y '' closedRectangle tl tr sb st) ∧
        volume (capChart Y '' closedRectangle tl tr sb st) < ⊤ ∧
        capChart Y '' closedRectangle tl tr sb st ⊆ modelOpenSquare) ∧
      ∀ m : ℕ,
        (∀ p ∈ capChartDomain,
          multiplierOperator (heightChartA (g0+eta) z Y) (heightChartB (g0+eta) z Y (m+3))
            (heightChartC (g0+eta) z Y (m+3)) (capPullback Y (verticalJet z (m+3))) p =
              capPullback Y (actualHighRemainder (g0+eta) z m) p) ∧
        ∀ L R bottom top b : ℝ,
          -2 < L → R < 2 → -2 < bottom → L ≤ R → bottom ≤ top → top < b → b ≤ 0 →
          0 < heightPhysicalCapConstant G Z d c e0 kappa (m+3) L R bottom top b ∧
          (∫ p in capChart Y '' closedRectangle L R bottom top,
            (coordPartial 0 (verticalJet z (m+3)) p)^2+(verticalJet z (m+4) p)^2) ≤
            heightPhysicalCapConstant G Z d c e0 kappa (m+3) L R bottom top b*
              ((∫ p in capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b,
                  (actualHighRemainder (g0+eta) z m p)^2)+
                (∫ p in capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b,
                  (verticalJet z (m+3) p)^2)) := by
  obtain ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hconf,hdisp50,hdisp,hall⟩ :=
    exists_C8_one_flow_all_high_cap_estimates hg hU hSU hz hG hZ hd hc he0 hgB hzB hdet hyy hEfloor
      hsmall hD hk hbackground hsupport hcentral
  obtain ⟨_,hsource,_,heq,_,_⟩ :=
    exists_global_triangularFlow_chart hq hV hSV hY hconf hstart hode
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hMq (p : Coord) (hp : p ∈ modelSquare) :
      |coordPartial 1 (hessianQuotient (g0+eta) z) p| ≤ M := hqB [1] (by norm_num) p hp
  have hJ (p : Coord) (hp : p ∈ capChartDomain) :=
    capChart_jacobian_bounds hq hV hSV hY hconf hstart hode hM hMq hp
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (g0+eta) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hyyO : ∀ p ∈ modelOpenSquare, covHessian (g0+eta) z p 1 1 ≠ 0 :=
    fun p hp => LowQuotient.denominator_ne_zero hc hyy p (modelOpenSquare_subset hp)
  have hsmall1 (p : Coord) (hp : p ∈ capChartDomain) :
      |hessianQuotient (g0+eta) z (capChart Y p)| ≤ 1 :=
    (hsmall _ (modelOpenSquare_subset (hmapO hp))).trans (by norm_num)
  refine ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hconf,hdisp50,hdisp,
    (fun tl tr sb st hbox => cap_closed_image_properties hYs hdisp hbox),?_⟩
  intro m
  obtain ⟨_,_,_,_,_,hPDE,hestimate⟩ := hall m
  refine ⟨hPDE,?_⟩
  intro L R bottom top b hL hR hbottom hLR hbt htop hb
  have hT : closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b ⊆ capChartDomain :=
    capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hS : closedRectangle L R bottom top ⊆ capChartDomain := by
    intro p hp
    exact ⟨⟨hL.trans_le hp.1.1,hp.1.2.trans_lt hR⟩,
      ⟨hbottom.trans_le hp.2.1,by linarith [hp.2.2]⟩⟩
  obtain ⟨hlo,hli,hlu,hri,hrr,hro,hao,hai,hau,hlx,hrx⟩ := capOuterRectangle_edges hL hR hbottom
  have hOT : capOuterLeft L ≤ capOuterRight R := by linarith
  have hOS : capOuterBottom bottom ≤ b := by linarith
  have hu := verticalJet_contDiffOn modelOpenSquare_isOpen hzO (m+3)
  have hf := actualHighRemainder_contDiffOn hgO modelOpenSquare_isOpen hzO
    (fun p hp => hD p (modelOpenSquare_subset hp)) hyyO m
  have hfI : ContinuousOn (actualHighRemainder (g0+eta) z m)
      (capChart Y '' closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b) :=
    hf.continuousOn.mono (by rintro _ ⟨p,hp,rfl⟩; exact hmapO (hT hp))
  have hcap := hestimate L R bottom top b hL hR hbottom hLR hbt htop hb
  rw [heightUniformCapEstimateRHS_eq_factors] at hcap
  have hp := cap_gradient_estimate_to_physical_images hYs hvar hode hsource heq hu
    modelOpenSquare_isOpen hmapO hLR hbt hOT hOS hS hT hsmall1 hJ hfI hcap
  refine ⟨heightPhysicalCapConstant_pos G Z d c e0 kappa (m+3) L R bottom top b,?_⟩
  change (∫ p in capChart Y '' closedRectangle L R bottom top,
      coordinateGradientSquare (verticalJet z (m+3)) p) ≤ _
  exact hp

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SixVariableQ
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem sixVariableQ_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (sixVariableQ g) (darbouxQStateDomain g U) :=
  (sixVariableP_contDiffOn (swappedMetric_smoothPositive hg)
    (coordinateSwap_preimage_isOpen hU)).comp qToPState_contDiff.contDiffOn
      (fun _ hw => qToPState_mem_domain hg hU hw)

theorem sixVariableQ_mixed_axis {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    fderiv ℝ (sixVariableQ g) w (Pi.single 4 1) =
      2 * (stateMixed g w / stateQDenominator g w) := by
  have hd := ((sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [fderiv_axis_eq_deriv_update hd]
  have heq : (fun t => sixVariableQ g (Function.update w 4 t)) =
      (fun t => solvedDarbouxQ g (statePoint w) t (w 5) (stateGradient w)) :=
    funext (sixVariableQ_update_mixed hg hU hw.1)
  rw [heq, solvedDarbouxQ_deriv_b g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2]
  rfl

theorem sixVariableQ_xx_axis {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    fderiv ℝ (sixVariableQ g) w (Pi.single 5 1) =
      -((stateMixed g w / stateQDenominator g w) ^ 2 +
        gaussianCurvature g (statePoint w) * stateEnergy g w / (stateQDenominator g w) ^ 2) := by
  have hd := ((sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [fderiv_axis_eq_deriv_update hd]
  have heq : (fun t => sixVariableQ g (Function.update w 5 t)) =
      (fun t => solvedDarbouxQ g (statePoint w) (w 4) t (stateGradient w)) :=
    funext (sixVariableQ_update_xx hg hU hw.1)
  rw [heq, solvedDarbouxQ_deriv_c g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2]
  rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QPrincipal
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qFirstCoefficient_contDiffOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (qFirstCoefficient g i) (darbouxQStateDomain g U) :=
  ((sixVariableQ_contDiffOn hg hU).fderiv_of_isOpen
    (darbouxQStateDomain_isOpen hg hU) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const

theorem q_principal_discriminant {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    (qFirstCoefficient g 4 w / 2) ^ 2 + qFirstCoefficient g 5 w =
      -(gaussianCurvature g (statePoint w) * stateEnergy g w) / (stateQDenominator g w) ^ 2 := by
  unfold qFirstCoefficient
  rw [sixVariableQ_mixed_axis hg hU hw, sixVariableQ_xx_axis hg hU hw]
  ring

theorem q_mixed_coefficient_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord}
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) :
    qFirstCoefficient g 4 (qSolutionJet z p) =
      2 * (covHessian g z p 0 1 / covHessian g z p 0 0) := by
  unfold qFirstCoefficient
  rw [sixVariableQ_mixed_axis hg hU (qSolutionJet_mem_domain hp hxx),
    stateQDenominator_qSolutionJet]
  unfold stateMixed
  rw [statePoint_qSolutionJet, stateGradient_qSolutionJet]
  rfl

theorem q_xx_coefficient_at_height {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    qFirstCoefficient g 5 (qSolutionJet z p) =
      -(covHessian g z p 1 1 / covHessian g z p 0 0) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  unfold qFirstCoefficient
  rw [sixVariableQ_xx_axis hg hU (qSolutionJet_mem_domain hp hxx),
    stateQDenominator_qSolutionJet]
  simp only [stateMixed, stateEnergy, statePoint_qSolutionJet, stateGradient_qSolutionJet]
  change -((jetMixed g p (coordPartial 0 (coordPartial 1 z) p)
    (fun i => coordPartial i z p) / covHessian g z p 0 0) ^ 2 +
      gaussianCurvature g p * jetEnergy g p (fun i => coordPartial i z p) /
        (covHessian g z p 0 0) ^ 2) = _
  rw [jetMixed_at_height, jetEnergy_at_height hg hp z]
  field_simp [hxx]
  nlinarith [hdet]

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ActualShearHyperbolicity
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem sheared_principal_coefficients {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ U)
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p))
    (hd : shearTimeFactor g z q0 p ≠ 0) :
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 ∧
    qFirstCoefficient (metricInShearCoordinates g q0) 4
        (qSolutionJet (heightInShearCoordinates z q0) p) =
      2 * (hessianQuotient g z (inverseShearCoordinates q0 p) - q0) /
        shearTimeFactor g z q0 p ∧
    qFirstCoefficient (metricInShearCoordinates g q0) 5
        (qSolutionJet (heightInShearCoordinates z q0) p) = -1 / shearTimeFactor g z q0 p := by
  have hgS := metricInShearCoordinates_smoothPositive hg q0
  have hzS := heightInShearCoordinates_contDiffOn hz q0
  have hUS := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hfac : covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 =
      shearTimeFactor g z q0 p * covHessian g z (inverseShearCoordinates q0 p) 1 1 :=
    sheared_Hxx_factor hg hz hU q0 hp hyy hD
  have hxx : covHessian (metricInShearCoordinates g q0)
      (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero hd hyy
  obtain ⟨h11, h01, h00⟩ := covHessian_shear_entries hg hz hU q0 hp
  refine ⟨hxx, ?_, ?_⟩
  · rw [q_mixed_coefficient_at_height hgS hUS hp hxx, h01, hfac]
    unfold hessianQuotient
    field_simp [hd, hyy]
  · rw [q_xx_coefficient_at_height hgS hUS hzS hp hxx
      (darboux_in_shear_coordinates hg hz hU q0 hp hD), h11, hfac]
    field_simp [hd, hyy]

theorem actual_shear_hyperbolicity {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U)
    (hU : IsOpen U) {q0 kappa e M v : ℝ} {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ U) (hkappa : 0 < kappa) (he : 0 < e)
    (hv : 0 < v) (hvBound : v ^ 2 ≤ kappa * e / (2 * M ^ 2))
    (hyy : covHessian g z (inverseShearCoordinates q0 p) 1 1 ≠ 0)
    (hH : |covHessian g z (inverseShearCoordinates q0 p) 1 1| ≤ M)
    (hE : e ≤ heightEnergy g z (inverseShearCoordinates q0 p))
    (hK : gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2)
    (hq : |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * (100 * (1 + v⁻¹))))
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) *
        heightEnergy g z (inverseShearCoordinates q0 p)) :
    v ^ 2 / 2 ≤ -shearTimeFactor g z q0 p ∧
    covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 ∧
    0 < qFirstCoefficient (metricInShearCoordinates g q0) 5
      (qSolutionJet (heightInShearCoordinates z q0) p) ∧
    |qFirstCoefficient (metricInShearCoordinates g q0) 4
      (qSolutionJet (heightInShearCoordinates z q0) p)| +
        Real.sqrt (qFirstCoefficient (metricInShearCoordinates g q0) 5
          (qSolutionJet (heightInShearCoordinates z q0) p)) < (100 * (1 + v⁻¹)) / 4 := by
  have ha : gaussianCurvature g (inverseShearCoordinates q0 p) *
      darbouxG g z (inverseShearCoordinates q0 p) ≤ -(v ^ 2) :=
    negative_curvature_factor hkappa he hyy hK hE hH hvBound
  obtain ⟨hb, hspeed⟩ := shear_width_smallness hv hq
  have hfactor := shear_time_factor_bound hv hb ha
  have hdneg : shearTimeFactor g z q0 p < 0 := by
    have hv2 : 0 < v ^ 2 / 2 := half_pos (sq_pos_of_pos hv)
    change v ^ 2 / 2 ≤ -shearTimeFactor g z q0 p at hfactor
    linarith
  obtain ⟨hxx, hP, hS⟩ := sheared_principal_coefficients hg hz hU q0 hp hyy hD hdneg.ne
  obtain ⟨hSpos, hchar⟩ := shear_principal_speed hv hb ha
  refine ⟨hfactor, hxx, ?_, ?_⟩
  · rw [hS]
    exact hSpos
  · rw [hP, hS]
    exact hchar.trans_lt hspeed

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem sixVariableQ_contDiffAt_solutionJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) :
    ContDiffAt ℝ ∞ (sixVariableQ g) (qSolutionJet z p) :=
  (sixVariableQ_contDiffOn hg hU).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds (qSolutionJet_mem_domain hp hxx))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QHighEquation
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem heightQCoefficient_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (i : Fin 6) :
    ContDiffOn ℝ ∞ (heightQCoefficient g z i) U :=
  (qFirstCoefficient_contDiffOn hg hU i).comp (qSolutionJet_contDiffOn hU hz)
    (fun p hp => qSolutionJet_mem_domain hp (hxx p hp))

theorem actualQ_top_chain_expansion
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (hp : coordinatePoint x y ∈ U) (m : ℕ) :
    iteratedDeriv (m + 3) (sixVariableQ g ∘ qSolutionJetCurve z y) x =
      chainTerm (sixVariableQ g) (qSolutionJetCurve z y) (ChainWord.single (m + 3)) x +
      (m + 3 : ℝ) * chainTerm (sixVariableQ g) (qSolutionJetCurve z y)
        (ChainWord.pair 1 (m + 2)) x +
      chainSum (sixVariableQ g) (qSolutionJetCurve z y) (topResidualWords m) x := by
  let I : Set ℝ := {t | coordinatePoint t y ∈ U}
  have hI : IsOpen I := hU.preimage (horizontalPoint_contDiff y).continuous
  have hJ : ContDiffOn ℝ ∞ (qSolutionJetCurve z y) I := by
    intro t ht
    exact (qSolutionJetCurve_contDiffAt hU hz ht).contDiffWithinAt
  have hmap : MapsTo (qSolutionJetCurve z y) I (darbouxQStateDomain g U) := by
    intro t ht
    exact qSolutionJet_mem_domain ht (hxx _ ht)
  exact top_chain_expansion (darbouxQStateDomain_isOpen hg hU) hI
    (sixVariableQ_contDiffOn hg hU) hJ hmap m x hp

theorem sixVariableQ_second_zero_spatial_direction
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ r ∈ U, covHessian g z r 0 0 ≠ 0) (hp : p ∈ U)
    (v : DarbouxState) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)
        ![coordPartial 0 (qSolutionJet z) p, v] =
      coordPartial 0 (heightQCoefficient g z 2) p * v 2 +
        coordPartial 0 (heightQCoefficient g z 3) p * v 3 +
        coordPartial 0 (heightQCoefficient g z 4) p * v 4 +
        coordPartial 0 (heightQCoefficient g z 5) p * v 5 := by
  rw [second_fderiv_comp_constant_direction_xi
    (sixVariableQ_contDiffAt_solutionJet hg hU hp (hxx _ hp))
    (((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  have heq : (fun r => fderiv ℝ (sixVariableQ g) (qSolutionJet z r) v) =
      (fun r => heightQCoefficient g z 2 r * v 2 + heightQCoefficient g z 3 r * v 3 +
        heightQCoefficient g z 4 r * v 4 + heightQCoefficient g z 5 r * v 5) :=
    funext (fun r => sixVariableQ_zero_spatial_direction g (qSolutionJet z r) v hv0 hv1)
  have hc (i : Fin 6) := ((heightQCoefficient_contDiffOn hg hU hz hxx i).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := ((((hc 2).hasFDerivAt.mul_const (v 2)).add
    ((hc 3).hasFDerivAt.mul_const (v 3))).add
      ((hc 4).hasFDerivAt.mul_const (v 4))).add ((hc 5).hasFDerivAt.mul_const (v 5))
  simp only [Pi.add_def] at hd
  rw [heq]
  unfold coordPartial
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem actualQ_pair_extract_secondJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (hp : coordinatePoint x y ∈ U) (n : ℕ) (hn : 2 ≤ n) :
    chainTerm (sixVariableQ g) (qSolutionJetCurve z y) (ChainWord.pair 1 n) x =
      qSecondJetCorrection g z (horizontalJet z (n + 1)) (coordinatePoint x y) +
        qFirstJetPairRemainder g z n (coordinatePoint x y) := by
  have hfirst : iteratedDeriv 1 (qSolutionJetCurve z y) x =
      coordPartial 0 (qSolutionJet z) (coordinatePoint x y) :=
    horizontalJet_slice hU (qSolutionJet_contDiffOn hU hz) y 1 x hp
  rw [chainTerm_pair_eq, hfirst, qSolutionJetCurve_iteratedDeriv hU hz hp n hn]
  simp only [qSolutionJetCurve]
  rw [
    sixVariableQ_second_zero_spatial_direction hg hU hz hxx hp _ (by rfl) (by rfl)]
  unfold qSecondJetCorrection qFirstJetPairRemainder
  rw [coordPartial_comm (horizontalJet_contDiffOn hU hz n) hU hp 0 1]
  change
    coordPartial 0 (heightQCoefficient g z 2) (coordinatePoint x y) *
      coordPartial 0 (horizontalJet z n) (coordinatePoint x y) +
    coordPartial 0 (heightQCoefficient g z 3) (coordinatePoint x y) *
      coordPartial 1 (horizontalJet z n) (coordinatePoint x y) +
    coordPartial 0 (heightQCoefficient g z 4) (coordinatePoint x y) *
      coordPartial 1 (coordPartial 0 (horizontalJet z n)) (coordinatePoint x y) +
    coordPartial 0 (heightQCoefficient g z 5) (coordinatePoint x y) *
      coordPartial 0 (coordPartial 0 (horizontalJet z n)) (coordinatePoint x y) =
    coordPartial 0 (heightQCoefficient g z 4) (coordinatePoint x y) *
      coordPartial 1 (coordPartial 0 (horizontalJet z n)) (coordinatePoint x y) +
    coordPartial 0 (heightQCoefficient g z 5) (coordinatePoint x y) *
      coordPartial 0 (coordPartial 0 (horizontalJet z n)) (coordinatePoint x y) + _
  ring

theorem actual_differentiated_Q
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (hp : coordinatePoint x y ∈ U) (m : ℕ) :
    coordPartial 1 (coordPartial 1 (horizontalJet z (m + 3))) (coordinatePoint x y) =
      qDirectLinearization g z (horizontalJet z (m + 3)) (coordinatePoint x y) +
        (m + 3 : ℝ) * qSecondJetCorrection g z (horizontalJet z (m + 3)) (coordinatePoint x y) +
        actualQHighRemainder g z m (coordinatePoint x y) := by
  have heq : (fun t => coordPartial 1 (coordPartial 1 z) (coordinatePoint t y)) =ᶠ[𝓝 x]
      sixVariableQ g ∘ qSolutionJetCurve z y := by
    filter_upwards [(hU.preimage (horizontalPoint_contDiff y).continuous).mem_nhds hp] with t ht
    exact (darbouxDet_iff_sixVariableQ hg hU hz ht (hxx _ ht)).1 (hD _ ht)
  have htop := actualQ_top_chain_expansion hg hU hz hxx hp m
  rw [← heq.iteratedDeriv_eq (m + 3)] at htop
  rw [horizontalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1)
      y (m + 3) x hp, horizontalJet_two_coordPartials hU hz hp (m + 3) 1 1,
    actualQ_single_linearization hU hz hp (m + 3) (by omega),
    actualQ_pair_extract_secondJet hg hU hz hxx hp (m + 2) (by omega),
    qChainSum_eq_coordinateChainSum hU hz hp] at htop
  unfold actualQHighRemainder
  convert htop using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem actual_Q_hyperbolic_equation
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (m : ℕ) {p : Coord} (hp : p ∈ U) :
    hyperbolicOperator (heightQCoefficient g z 4) (heightQCoefficient g z 5)
      (horizontalJet z (m + 3)) p =
      qHighBTheta g z (m + 3) p * coordPartial 1 (horizontalJet z (m + 3)) p +
        qHighBXi g z (m + 3) p * coordPartial 0 (horizontalJet z (m + 3)) p +
        actualQHighRemainder g z m p := by
  have he := actual_differentiated_Q hg hU hz hD hxx
    (x := p 0) (y := p 1) (by simpa only [point_eta] using hp) m
  rw [point_eta] at he
  unfold hyperbolicOperator qDirectLinearization qSecondJetCorrection qHighBTheta qHighBXi at *
  rw [he]
  push_cast
  ring

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QResidualFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology Matrix BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem qCoordinateChainCoefficient_continuousOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (qCoordinateChainCoefficient g z w r) U := by
  intro p hp
  have hQ := sixVariableQ_contDiffAt_solutionJet hg hU hp (hxx p hp)
  have houter := (hQ.differentiableAt_iteratedFDeriv (m := w.arity)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl w.arity)).continuousAt
  have hjet := ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).continuousAt
  have heval := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.arity => DarbouxState) ℝ
    (fun i => Pi.single (r i) (1 : ℝ))).continuous.continuousAt
      (x := iteratedFDeriv ℝ w.arity (sixVariableQ g) (qSolutionJet z p))
  exact ((heval.comp houter).comp hjet).continuousWithinAt

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QResidualL2
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Analytic

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord}

theorem qCoordinateScalarTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (fun p => qCoordinateChainCoefficient g z w r p *
      ∏ i, qCoordinateChainFactor z w r i p) U :=
  (qCoordinateChainCoefficient_continuousOn hg hU hz hxx w r).mul
    (continuousOn_finsetProd Finset.univ (fun i _ =>
      qCoordinateChainFactor_continuousOn hU hz w r i))

theorem qCoordinateChainTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (w : ChainWord) :
    ContinuousOn (qCoordinateChainTerm g z w) U := by
  have he : qCoordinateChainTerm g z w = fun p => ∑ r : Fin w.arity → Fin 6,
      qCoordinateChainCoefficient g z w r p * ∏ i, qCoordinateChainFactor z w r i p :=
    funext (qCoordinateChainTerm_scalar_expansion g z w)
  rw [he]
  exact continuousOn_finsetSum Finset.univ
    (fun r _ => qCoordinateScalarTerm_continuousOn hg hU hz hxx w r)

theorem qCoordinateChainSum_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (ws : List ChainWord) :
    ContinuousOn (qCoordinateChainSum g z ws) U := by
  induction ws with
  | nil => exact continuousOn_const
  | cons w ws ih => exact (qCoordinateChainTerm_continuousOn hg hU hz hxx w).add ih

theorem qFirstJetPairRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (n : ℕ) :
    ContinuousOn (qFirstJetPairRemainder g z n) U := by
  have hc (i : Fin 6) := (partial_contDiffOn (heightQCoefficient_contDiffOn hg hU hz hxx i) hU 0).continuousOn
  have hf (i : Fin 2) := (partial_contDiffOn (horizontalJet_contDiffOn hU hz n) hU i).continuousOn
  exact ((hc 2).mul (hf 0)).add ((hc 3).mul (hf 1))

theorem qFirstJetPairRemainder_slice_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right Cfirst : ℝ} {N : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) (hCfirst : 0 ≤ Cfirst)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right N H)
    (hfirst2 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 2) (coordinatePoint x theta)| ≤ Cfirst)
    (hfirst3 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 3) (coordinatePoint x theta)| ≤ Cfirst) :
    eLpNorm (fun x => qFirstJetPairRemainder g z N (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qPairSliceBudget Cfirst H := by
  have hf (i : Fin 2) : eLpNorm (fun x => coordPartial i (horizontalJet z N) (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ (H : ℝ≥0∞) := by
    have he : (fun x => coordPartial i (horizontalJet z N) (coordinatePoint x theta)) =ᵐ[
        volume.restrict (Icc left right)] (fun x => spatialJet (spatialFirstJet z i) N (coordinatePoint x theta)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      rw [← horizontalJet_coordPartial hU hz i N _ (hseg x hx), horizontalJet_eq_spatialJet]
      rfl
    rw [eLpNorm_congr_ae he]
    exact hL2 i N le_rfl
  have hm (i : Fin 6) (j : Fin 2) : AEStronglyMeasurable
      (fun x => coordPartial 0 (heightQCoefficient g z i) (coordinatePoint x theta) *
        coordPartial j (horizontalJet z N) (coordinatePoint x theta))
      (volume.restrict (Icc left right)) :=
    (smooth_slice_memLp_two
      ((partial_contDiffOn (heightQCoefficient_contDiffOn hg hU hz hxx i) hU 0).continuousOn.mul
        (partial_contDiffOn (horizontalJet_contDiffOn hU hz N) hU j).continuousOn) hseg).aestronglyMeasurable
  have h0 := (real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable
    hCfirst hfirst2 (hm 2 0)).trans (mul_le_mul' le_rfl (hf 0))
  have h1 := (real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable
    hCfirst hfirst3 (hm 3 1)).trans (mul_le_mul' le_rfl (hf 1))
  exact (eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add h0 h1)

theorem actualQHighRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (m : ℕ) :
    ContinuousOn (actualQHighRemainder g z m) U :=
  (qCoordinateChainSum_continuousOn hg hU hz hxx (topResidualWords m)).add
    (continuousOn_const.mul (qFirstJetPairRemainder_continuousOn hg hU hz hxx (m + 2)))

theorem actualQHighRemainder_slice_memLp_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (m : ℕ)
    {theta left right : ℝ} (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U) :
    MemLp (fun x => actualQHighRemainder g z m (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) :=
  smooth_slice_memLp_two (actualQHighRemainder_continuousOn hg hU hz hxx m) hseg

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QResidualActive
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE
open SmoothLocal.Hyperbolic SmoothLocal.Analytic

theorem qCoordinateChainTerm_slice_eLpNorm_two_active
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    {w : ChainWord} (hw : w ∈ topResidualWords m)
    (hcoeff : ∀ r, QActiveComponents w r → ∀ x ∈ Icc left right,
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C) :
    eLpNorm (fun x => qCoordinateChainTerm g z w (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qWordSliceBudget C lengthFloor left right H w := by
  classical
  have he : (fun x => qCoordinateChainTerm g z w (coordinatePoint x theta)) = fun x =>
      ∑ r : Fin w.arity → Fin 6, qCoordinateChainCoefficient g z w r (coordinatePoint x theta) *
        ∏ i, qCoordinateChainFactor z w r i (coordinatePoint x theta) :=
    funext (fun x => qCoordinateChainTerm_scalar_expansion g z w (coordinatePoint x theta))
  rw [he]
  apply finite_sum_eLpNorm_two (μ := volume) (U := Icc left right) Finset.univ _
    (fun _ => ‖C‖ₑ * spatialProductL2Budget lengthFloor left right H w.arity)
  · intro r _
    exact (smooth_slice_memLp_two
      (qCoordinateScalarTerm_continuousOn hg hU hz hxx w r) hseg).aestronglyMeasurable
  · intro r _
    by_cases hactive : QActiveComponents w r
    · exact (real_interval_coefficient_eLpNorm_two_of_aestronglyMeasurable hC (hcoeff r hactive)
        (smooth_slice_memLp_two
          (qCoordinateScalarTerm_continuousOn hg hU hz hxx w r) hseg).aestronglyMeasurable).trans
        (mul_le_mul' le_rfl (q_residual_product_eLpNorm_two hU hz hseg hlength hwidth hm hL2 hw r))
    · have hzero : (fun x => qCoordinateChainCoefficient g z w r (coordinatePoint x theta) *
          ∏ i, qCoordinateChainFactor z w r i (coordinatePoint x theta)) =ᵐ[
          volume.restrict (Icc left right)] (0 : ℝ → ℝ) := by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        rw [qCoordinateChainProduct_eq_zero_of_inactive hU hz (hseg x hx) w
          (topResidualWords_properties m w hw).1 r hactive, mul_zero]
        rfl
      rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
      positivity

theorem qCoordinateChainSum_slice_eLpNorm_two_active
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, QActiveComponents w r → ∀ x ∈ Icc left right,
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C)
    (ws : List ChainWord) (hws : ∀ w ∈ ws, w ∈ topResidualWords m) :
    eLpNorm (fun x => qCoordinateChainSum g z ws (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qChainSliceBudget C lengthFloor left right H ws := by
  induction ws with
  | nil =>
      change eLpNorm (0 : ℝ → ℝ) 2 (volume.restrict (Icc left right)) ≤ 0
      simp
  | cons w ws ih =>
      have hw := hws w List.mem_cons_self
      have ht := qCoordinateChainTerm_slice_eLpNorm_two_active hg hU hz hxx hseg hlength hwidth hm hC
        hL2 hw (hcoeff w hw)
      have hs := ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
      change eLpNorm (fun x => qCoordinateChainTerm g z w (coordinatePoint x theta) +
        qCoordinateChainSum g z ws (coordinatePoint x theta)) 2 (volume.restrict (Icc left right)) ≤
          qWordSliceBudget C lengthFloor left right H w + qChainSliceBudget C lengthFloor left right H ws
      exact (eLpNorm_add_le (hf := by exact aesm_slice (qCoordinateChainTerm_continuousOn hg hU hz hxx w) hseg) (hg := by exact aesm_slice (qCoordinateChainSum_continuousOn hg hU hz hxx ws) hseg) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add ht hs)

theorem actualQHighRemainder_slice_eLpNorm_two_active
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0)
    {theta left right lengthFloor C Cfirst : ℝ} {m : ℕ} {H : ℝ≥0}
    (hseg : ∀ x ∈ Icc left right, coordinatePoint x theta ∈ U)
    (hlength : 0 < lengthFloor) (hwidth : lengthFloor ≤ right - left)
    (hm : 8 ≤ m + 3) (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst)
    (hL2 : SpatialSliceL2Bound (spatialFirstJet z) theta left right (m + 2) H)
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, QActiveComponents w r → ∀ x ∈ Icc left right,
      |qCoordinateChainCoefficient g z w r (coordinatePoint x theta)| ≤ C)
    (hfirst2 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 2) (coordinatePoint x theta)| ≤ Cfirst)
    (hfirst3 : ∀ x ∈ Icc left right, |coordPartial 0 (heightQCoefficient g z 3) (coordinatePoint x theta)| ≤ Cfirst) :
    eLpNorm (fun x => actualQHighRemainder g z m (coordinatePoint x theta)) 2
      (volume.restrict (Icc left right)) ≤ qRemainderSliceBudget C Cfirst lengthFloor left right H m := by
  have hs := qCoordinateChainSum_slice_eLpNorm_two_active hg hU hz hxx hseg hlength hwidth hm hC
    hL2 hcoeff (topResidualWords m) (fun _ wordMem => wordMem)
  have hp := qFirstJetPairRemainder_slice_eLpNorm_two hg hU hz hxx hseg hCfirst hL2 hfirst2 hfirst3
  have hscaled : eLpNorm (fun x => (m + 3 : ℝ) * qFirstJetPairRemainder g z (m + 2) (coordinatePoint x theta))
      2 (volume.restrict (Icc left right)) ≤ ‖(m + 3 : ℝ)‖ₑ * qPairSliceBudget Cfirst H := by
    change eLpNorm ((m + 3 : ℝ) • (fun x => qFirstJetPairRemainder g z (m + 2) (coordinatePoint x theta)))
      2 (volume.restrict (Icc left right)) ≤ _
    rw [eLpNorm_const_smul (𝕜 := ℝ) (F := ℝ)]
    exact mul_le_mul' le_rfl hp
  exact (eLpNorm_add_le (hf := by exact aesm_slice (qCoordinateChainSum_continuousOn hg hU hz hxx (topResidualWords m)) hseg) (hg := by exact aesm_slice (h := fun p => ((m : ℝ) + 3) * qFirstJetPairRemainder g z (m + 2) p) (continuousOn_const.mul (qFirstJetPairRemainder_continuousOn hg hU hz hxx (m + 2))) hseg) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add hs hscaled)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSpatialRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem qFixedTimeQ_iteratedFDeriv
    {g : MetricField} {U : Set Coord} {theta : ℝ} {v : QSpatialState}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hv : v ∈ qFixedTimeDomain g U theta) (n : ℕ) :
    iteratedFDeriv ℝ n (qFixedTimeQ g theta) v =
      (iteratedFDeriv ℝ n (sixVariableQ g) (qFixedTimeState theta v)).compContinuousLinearMap
        (fun _ => qSpatialCLM) := by
  let c : DarbouxState := Pi.single 1 theta
  let O : Set DarbouxState := (fun w : DarbouxState => w + c) ⁻¹' darbouxQStateDomain g U
  have hO : IsOpen O := (darbouxQStateDomain_isOpen hg hU).preimage (by fun_prop)
  have hF : ContDiffOn ℝ ∞ (fun w : DarbouxState => sixVariableQ g (w + c)) O :=
    (sixVariableQ_contDiffOn hg hU).comp (by fun_prop) (fun _ hw => hw)
  have hpre : IsOpen (qSpatialCLM ⁻¹' O) := hO.preimage qSpatialCLM.continuous
  have hp : qSpatialCLM v ∈ O := hv
  have he := qSpatialCLM.iteratedFDerivWithin_comp_right hF hO.uniqueDiffOn hpre.uniqueDiffOn hp
    (i := n) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen n hpre hp,
    iteratedFDerivWithin_of_isOpen n hO hp,
    iteratedFDeriv_comp_add_right n c (qSpatialCLM v)] at he
  exact he

theorem qCoordinateChainCoefficient_eq_fixedTime
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) (w : ChainWord) (r : Fin w.arity → Fin 6)
    (hactive : QActiveComponents w r) :
    qCoordinateChainCoefficient g z w r p =
      iteratedFDeriv ℝ w.arity (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))
        (fun i => Pi.single (qSpatialIndex (r i)) 1) := by
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hv : qSpatialProjection (qSolutionJet z p) ∈ qFixedTimeDomain g U (p 1) := by
    change qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) ∈ darbouxQStateDomain g U
    rw [he]
    exact qSolutionJet_mem_domain hp hxx
  rw [qFixedTimeQ_iteratedFDeriv hg hU hv w.arity,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, he]
  unfold qCoordinateChainCoefficient
  congr 1
  funext i
  rw [qSpatialCLM_single, qSpatialAxis_index (hactive i).1]

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QFirstSpatialBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem heightQCoefficient_xi_eq_fixedTime_second
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) (i : Fin 6) (hi : i ≠ 1) :
    coordPartial 0 (heightQCoefficient g z i) p =
      iteratedFDeriv ℝ 2 (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))
        ![qSpatialProjection (coordPartial 0 (qSolutionJet z) p), Pi.single (qSpatialIndex i) 1] := by
  have he : qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) = qSolutionJet z p :=
    qFixedTimeState_projection (qSolutionJet z p)
  have hv : qSpatialProjection (qSolutionJet z p) ∈ qFixedTimeDomain g U (p 1) := by
    change qFixedTimeState (p 1) (qSpatialProjection (qSolutionJet z p)) ∈ darbouxQStateDomain g U
    rw [he]
    exact qSolutionJet_mem_domain hp hxx
  have htime : coordPartial 0 (qSolutionJet z) p 1 = 0 := by
    have hh := congrArg (fun v : DarbouxState => v 1)
      (coordinate_qSolutionJet_horizontal_positive hU hz hp 1 (by norm_num))
    exact hh
  rw [qFixedTimeQ_iteratedFDeriv hg hU hv 2,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, he]
  have hvec : (fun j : Fin 2 => qSpatialCLM
      (![qSpatialProjection (coordPartial 0 (qSolutionJet z) p), Pi.single (qSpatialIndex i) 1] j)) =
      ![coordPartial 0 (qSolutionJet z) p, Pi.single i 1] := by
    funext j
    fin_cases j
    · exact qSpatialCLM_projection_of_time_zero htime
    · change qSpatialCLM (Pi.single (qSpatialIndex i) 1) = Pi.single i 1
      rw [qSpatialCLM_single, qSpatialAxis_index hi]
  rw [hvec]
  exact (second_fderiv_comp_constant_direction_xi
    (sixVariableQ_contDiffAt_solutionJet hg hU hp hxx)
    (((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (Pi.single i 1)).symm

theorem heightQCoefficient_xi_bound_of_fixedTime_second
    {g : MetricField} {z : Coord → ℝ} {U S : Set Coord} {Z C : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hSU : S ⊆ U) (hzB : CoordinateBound z S 3 Z) (hC : 0 ≤ C)
    {p : Coord} (hp : p ∈ S) (hxx : covHessian g z p 0 0 ≠ 0)
    (hQ : ‖iteratedFDeriv ℝ 2 (qFixedTimeQ g (p 1)) (qSpatialProjection (qSolutionJet z p))‖ ≤ C)
    (i : Fin 6) (hi : i ≠ 1) :
    |coordPartial 0 (heightQCoefficient g z i) p| ≤ C * max 1 Z := by
  rw [heightQCoefficient_xi_eq_fixedTime_second hg hU hz (hSU hp) hxx i hi, ← Real.norm_eq_abs]
  have hd := (qSpatialProjection_norm_le (coordPartial 0 (qSolutionJet z) p)).trans
    (coordPartial_qSolutionJet_xi_norm_bound hU hz hSU hzB hp)
  have hb := (iteratedFDeriv ℝ 2 (qFixedTimeQ g (p 1))
    (qSpatialProjection (qSolutionJet z p))).le_opNorm
      ![qSpatialProjection (coordPartial 0 (qSolutionJet z) p), Pi.single (qSpatialIndex i) (1 : ℝ)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.norm_single, norm_one, mul_one] at hb
  exact hb.trans (mul_le_mul hQ hd (norm_nonneg _) hC)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QEnergyApplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem qHighBTheta_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (ell : ℕ) :
    ContDiffOn ℝ ∞ (qHighBTheta g z ell) U :=
  (heightQCoefficient_contDiffOn hg hU hz hxx 3).add (contDiffOn_const.mul
    (partial_contDiffOn (heightQCoefficient_contDiffOn hg hU hz hxx 4) hU 0))

theorem qHighBXi_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (ell : ℕ) :
    ContDiffOn ℝ ∞ (qHighBXi g z ell) U :=
  (heightQCoefficient_contDiffOn hg hU hz hxx 2).add (contDiffOn_const.mul
    (partial_contDiffOn (heightQCoefficient_contDiffOn hg hU hz hxx 5) hU 0))

theorem actualQHighRemainder_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hxx : ∀ p ∈ U, covHessian g z p 0 0 ≠ 0) (m : ℕ) :
    ContDiffOn ℝ ∞ (actualQHighRemainder g z m) U := by
  have hu := horizontalJet_contDiffOn hU hz (m + 3)
  have hx := partial_contDiffOn hu hU 0
  have ht := partial_contDiffOn hu hU 1
  have hP := heightQCoefficient_contDiffOn hg hU hz hxx 4
  have hS := heightQCoefficient_contDiffOn hg hU hz hxx 5
  have hbt := qHighBTheta_contDiffOn hg hU hz hxx (m + 3)
  have hbx := qHighBXi_contDiffOn hg hU hz hxx (m + 3)
  have hf := ((((partial_contDiffOn ht hU 1).sub
    (hP.mul (partial_contDiffOn ht hU 0))).sub
      (hS.mul (partial_contDiffOn hx hU 0))).sub (hbt.mul ht)).sub (hbx.mul hx)
  apply hf.congr
  intro p hp
  have he := actual_Q_hyperbolic_equation hg hU hz hD hxx m hp
  change actualQHighRemainder g z m p =
    coordPartial 1 (coordPartial 1 (horizontalJet z (m + 3))) p -
      heightQCoefficient g z 4 p * coordPartial 0 (coordPartial 1 (horizontalJet z (m + 3))) p -
      heightQCoefficient g z 5 p * coordPartial 0 (coordPartial 0 (horizontalJet z (m + 3))) p -
      qHighBTheta g z (m + 3) p * coordPartial 1 (horizontalJet z (m + 3)) p -
      qHighBXi g z (m + 3) p * coordPartial 0 (horizontalJet z (m + 3)) p
  unfold hyperbolicOperator at he
  linarith

theorem actual_Q_moving_slab_energy
    {g : MetricField} {z : Coord → ℝ} {radius lo hi xl xr a b speed s0 M : ℝ}
    (hg : SmoothPositiveOn g (coordinateRectangle radius lo hi))
    (hz : ContDiffOn ℝ ∞ z (coordinateRectangle radius lo hi))
    (hD : ∀ p ∈ coordinateRectangle radius lo hi,
      (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hxx : ∀ p ∈ coordinateRectangle radius lo hi, covHessian g z p 0 0 ≠ 0)
    (m : ℕ) (hradius : 0 < radius) (hab : a ≤ b) (hspeed : 0 ≤ speed)
    (hxl : -radius < xl) (hxr : xr < radius) (ha : a ∈ Ioo lo hi) (hb : b ∈ Ioo lo hi)
    (hlength : 2 * speed * (b - a) < xr - xl) (hs0 : 0 < s0) (hM : 0 ≤ M)
    (hSfloor : ∀ p ∈ shrinkingSlab xl xr a b speed, s0 ≤ heightQCoefficient g z 5 p)
    (hcoeff : ∀ p ∈ shrinkingSlab xl xr a b speed,
      |qHighBTheta g z (m + 3) p| ≤ M ∧ |qHighBXi g z (m + 3) p| ≤ M ∧
        |coordPartial 0 (heightQCoefficient g z 4) p| ≤ M ∧
        |coordPartial 0 (heightQCoefficient g z 5) p| ≤ M ∧
        |coordPartial 1 (heightQCoefficient g z 5) p| ≤ M)
    (hchar : ∀ p ∈ shrinkingSlab xl xr a b speed,
      |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) :
    Real.sqrt (movingEnergy xl xr a speed (heightQCoefficient g z 5) (horizontalJet z (m + 3)) b) ≤
      Real.exp ((8 * M * (1 + 1 / s0)) * (b - a)) *
        (Real.sqrt (∫ xi in xl..xr, energyDensity (heightQCoefficient g z 5)
          (horizontalJet z (m + 3)) (coordinatePoint xi a)) +
            ∫ t in a..b, movingSourceNorm xl xr a speed (actualQHighRemainder g z m) t) := by
  have hU := coordinateRectangle_isOpen radius lo hi
  apply moving_slab_energy_propagation
    (heightQCoefficient_contDiffOn hg hU hz hxx 4)
    (heightQCoefficient_contDiffOn hg hU hz hxx 5)
    (qHighBTheta_contDiffOn hg hU hz hxx (m + 3))
    (qHighBXi_contDiffOn hg hU hz hxx (m + 3))
    (horizontalJet_contDiffOn hU hz (m + 3))
    (actualQHighRemainder_contDiffOn hg hU hz hD hxx m)
    hradius hab hspeed hxl hxr ha hb hlength hs0 hM hSfloor hcoeff hchar
  intro p hp
  exact actual_Q_hyperbolic_equation hg hU hz hD hxx m
    (shrinkingSlab_subset_rectangle hab hspeed hxl hxr ha hb hlength hp)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualRemainderFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

theorem coordinateScalarTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (fun p => coordinateChainCoefficient g z w r p *
      ∏ i, coordinateChainFactor z w r i p) U := by
  exact (coordinateChainCoefficient_continuousOn hg hU hz hyy w r).mul
    (continuousOn_finsetProd Finset.univ
      (fun index _ => coordinateChainFactor_continuousOn hU hz w r index))

theorem coordinateChainTerm_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (w : ChainWord) :
    ContinuousOn (coordinateChainTerm g z w) U := by
  have h := continuousOn_finsetSum Finset.univ
    (fun indices _ => coordinateScalarTerm_continuousOn hg hU hz hyy w indices)
  exact h.congr (fun point _ => coordinateChainTerm_scalar_expansion g z w point)

theorem coordinateChainSum_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (ws : List ChainWord) :
    ContinuousOn (coordinateChainSum g z ws) U :=
  continuousOn_list_sum ws (fun word _ => coordinateChainTerm_continuousOn hg hU hz hyy word)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_ActualRemainderL2
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

variable {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}

theorem coordinateChainTerm_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    {w : ChainWord} (hw : w ∈ topResidualWords m)
    (hcoeff : ∀ r, ∀ p ∈ V, |coordinateChainCoefficient g z w r p| ≤ C) :
    eLpNorm (coordinateChainTerm g z w) 2 (volume.restrict V) ≤
      chainWordL2Budget C B H V (m + 3) w := by
  classical
  have hmeas (r : Fin w.arity → Fin 6) :
      AEStronglyMeasurable (fun p => coordinateChainCoefficient g z w r p *
        ∏ i, coordinateChainFactor z w r i p) (volume.restrict V) :=
    ((coordinateScalarTerm_continuousOn hg hU hz hyy w r).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hterm (r : Fin w.arity → Fin 6) :
      eLpNorm (fun p => coordinateChainCoefficient g z w r p *
        ∏ i, coordinateChainFactor z w r i p) 2 (volume.restrict V) ≤
        ‖C‖ₑ * chainProductL2Budget B H V (m + 3) :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (hcoeff r) (hmeas r)).trans
      (mul_le_mul' le_rfl (residual_product_eLpNorm_two hU hz hV hVU hm hB hlow hheight hw r))
  have he : coordinateChainTerm g z w = fun p =>
      ∑ r : Fin w.arity → Fin 6, coordinateChainCoefficient g z w r p *
        ∏ i, coordinateChainFactor z w r i p :=
    funext (coordinateChainTerm_scalar_expansion g z w)
  rw [he]
  exact finite_sum_eLpNorm_two Finset.univ _
    (fun _ => ‖C‖ₑ * chainProductL2Budget B H V (m + 3))
    (fun indices _ => hmeas indices) (fun indices _ => hterm indices)

theorem coordinateChainSum_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C)
    (ws : List ChainWord) (hws : ∀ w ∈ ws, w ∈ topResidualWords m) :
    eLpNorm (coordinateChainSum g z ws) 2 (volume.restrict V) ≤
      chainSumL2Budget C B H V (m + 3) ws := by
  induction ws with
  | nil =>
      change eLpNorm (0 : Coord → ℝ) 2 (volume.restrict V) ≤ 0
      simp
  | cons w ws ih =>
      have hw := hws w List.mem_cons_self
      have ht := coordinateChainTerm_eLpNorm_two hg hU hz hyy hV hVU hm hC hB
        hlow hheight hw (hcoeff w hw)
      have hs := ih (fun v hv => hws v (List.mem_cons_of_mem _ hv))
      change eLpNorm (fun p => coordinateChainTerm g z w p + coordinateChainSum g z ws p)
        2 (volume.restrict V) ≤
          chainWordL2Budget C B H V (m + 3) w + chainSumL2Budget C B H V (m + 3) ws
      exact (eLpNorm_add_le (hf := by exact ((coordinateChainTerm_continuousOn hg hU hz hyy w).mono hVU).aestronglyMeasurable hV) (hg := by exact ((coordinateChainSum_continuousOn hg hU hz hyy ws).mono hVU).aestronglyMeasurable hV) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
        (add_le_add ht hs)

theorem actualHighRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) :
    ContinuousOn (actualHighRemainder g z m) U :=
  (coordinateChainSum_continuousOn hg hU hz hyy (topResidualWords m)).add
    (continuousOn_const.mul (firstJetPairRemainder_continuousOn hg hU hz hyy (m + 2)))

theorem actualHighRemainder_eLpNorm_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {m : ℕ} (hm : 8 ≤ m + 3) {C Cfirst B : ℝ}
    (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C)
    (hfirst : ∀ i : Fin 2, ∀ p ∈ V, |coordPartial 1 (heightPFirst g z i) p| ≤ Cfirst) :
    eLpNorm (actualHighRemainder g z m) 2 (volume.restrict V) ≤
      actualHighRemainderL2Budget C Cfirst B H V m := by
  have hs := coordinateChainSum_eLpNorm_two hg hU hz hyy hV hVU hm hC hB
    hlow hheight hcoeff (topResidualWords m) (fun _ hw => hw)
  have hp := firstJetPairRemainder_eLpNorm_two hg hU hz hyy hV hVU hCfirst hheight hfirst
  have hscaled : eLpNorm (fun p => (m + 3 : ℝ) * firstJetPairRemainder g z (m + 2) p)
      2 (volume.restrict V) ≤ ‖(m + 3 : ℝ)‖ₑ * firstJetPairL2Budget Cfirst H := by
    change eLpNorm ((m + 3 : ℝ) • firstJetPairRemainder g z (m + 2))
      2 (volume.restrict V) ≤ _
    rw [eLpNorm_const_smul (𝕜 := ℝ) (F := ℝ)]
    exact mul_le_mul' le_rfl hp
  exact (eLpNorm_add_le (hf := by exact ((coordinateChainSum_continuousOn hg hU hz hyy (topResidualWords m)).mono hVU).aestronglyMeasurable hV) (hg := by exact ((show ContinuousOn (fun p => ((m : ℝ) + 3) * firstJetPairRemainder g z (m + 2) p) U from continuousOn_const.mul (firstJetPairRemainder_continuousOn hg hU hz hyy (m + 2))).mono hVU).aestronglyMeasurable hV) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add hs hscaled)

theorem actualHighRemainder_memLp_two
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVfinite : volume V < (⊤ : ℝ≥0∞))
    {m : ℕ} (hm : 8 ≤ m + 3) {C Cfirst B : ℝ}
    (hC : 0 ≤ C) (hCfirst : 0 ≤ Cfirst) (hB : 1 ≤ B) {H : ℝ≥0}
    (hlow : ∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
      ∀ p ∈ V, |heightStateFactor z n j p| ≤ B)
    (hheight : ∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
      eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hcoeff : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C)
    (hfirst : ∀ i : Fin 2, ∀ p ∈ V, |coordPartial 1 (heightPFirst g z i) p| ≤ Cfirst) :
    MemLp (actualHighRemainder g z m) 2 (volume.restrict V) := by
  refine ⟨((actualHighRemainder_continuousOn hg hU hz hyy m).mono hVU).aestronglyMeasurable hV, ?_⟩
  exact (actualHighRemainder_eLpNorm_two hg hU hz hyy hV hVU hm hC hCfirst hB
    hlow hheight hcoeff hfirst).trans_lt
      (actualHighRemainderL2Budget_lt_top C Cfirst B H hVfinite m)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QLowActualBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem heightQCoefficient_partial_eq_second
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hxx : covHessian g z p 0 0 ≠ 0) (i : Fin 6) (j : Fin 2) :
    coordPartial j (heightQCoefficient g z i) p =
      iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)
        ![coordPartial j (qSolutionJet z) p, Pi.single i 1] := by
  exact (second_fderiv_comp_constant_coordinate
    (sixVariableQ_contDiffAt_solutionJet hg hU hp hxx)
    (((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    j (Pi.single i 1)).symm

theorem heightQCoefficient_partial_bound_of_second
    {g : MetricField} {z : Coord → ℝ} {U S : Set Coord} {Z C : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hSU : S ⊆ U) (hzB : CoordinateBound z S 3 Z) (hC : 0 ≤ C)
    {p : Coord} (hp : p ∈ S) (hxx : covHessian g z p 0 0 ≠ 0)
    (hQ : ‖iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)‖ ≤ C)
    (i : Fin 6) (j : Fin 2) :
    |coordPartial j (heightQCoefficient g z i) p| ≤ C * max 1 Z := by
  rw [heightQCoefficient_partial_eq_second hg hU hz (hSU hp) hxx i j, ← Real.norm_eq_abs]
  have hd := coordPartial_qSolutionJet_norm_bound hU hz hSU hzB hp j
  have hb := (iteratedFDeriv ℝ 2 (sixVariableQ g) (qSolutionJet z p)).le_opNorm
    ![coordPartial j (qSolutionJet z) p, Pi.single i (1 : ℝ)]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Pi.norm_single, norm_one, mul_one] at hb
  exact hb.trans (mul_le_mul hQ hd (norm_nonneg _) hC)

theorem exists_same_region_Q_low_bound
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j k, k ≤ 4 → ∀ p ∈ S, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ i : Fin 6, ∀ p ∈ S,
        |heightQCoefficient g z i p| ≤ M ∧
          ∀ j : Fin 2, |coordPartial j (heightQCoefficient g z i) p| ≤ M := by
  obtain ⟨C, hC, hQ⟩ := exists_local_metric_Q_jet_bound G (max R Z) hG hd hc 2
  refine ⟨C * max 1 Z, mul_nonneg hC (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden i p hp
  have hxx : covHessian g z p 0 0 ≠ 0 := by
    intro he
    have hh := hden p hp
    rw [he, abs_zero] at hh
    linarith
  have hz2 : CoordinateBound z S 2 Z := fun ds hds p hp => hzB ds (by omega) p hp
  have hpoint := statePoint_qSolutionJet z p
  have hb (n : ℕ) (hn : n ≤ 2) :
      ‖iteratedFDeriv ℝ n (sixVariableQ g) (qSolutionJet z p)‖ ≤ C :=
    hQ g U hg hU (qSolutionJet z p) (by simpa only [hpoint] using hSU hp)
      (fun a b k hk => by simpa only [hpoint] using hgB a b k (by omega) p hp)
      (qSolutionJet_norm_bound_of_coordinateBound hR hz2 hcoords hp)
      (by simpa only [hpoint] using hdet p hp)
      (by simpa only [stateQDenominator_qSolutionJet] using hden p hp) n hn
  refine ⟨(heightQCoefficient_value_bound (hb 1 (by omega)) i).trans ?_, ?_⟩
  · exact le_mul_of_one_le_right hC (le_max_left _ _)
  · intro j
    exact heightQCoefficient_partial_bound_of_second hg hU hz hSU hzB hC hp hxx (hb 2 le_rfl) i j

theorem exists_same_region_Q_low_bound_of_coordinate
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) S 4 G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ i : Fin 6, ∀ p ∈ S,
        |heightQCoefficient g z i p| ≤ M ∧
          ∀ j : Fin 2, |coordPartial j (heightQCoefficient g z i) p| ≤ M := by
  obtain ⟨M, hM, hbound⟩ := exists_same_region_Q_low_bound (16 * G) R Z (by positivity) hR hd hc
  refine ⟨M, hM, ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden
  apply hbound g z U S hg hU hz hSU hcoords ?_ hzB hdet hden
  intro i j k hk p hp
  have hb := (hgB i j).full_jet_norm_bound (hg.1 i j) hU hSU hG hk hp
  have hpow : (2 : ℝ)^k ≤ 16 := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    norm_num at hh ⊢
    exact hh
  exact hb.trans (mul_le_mul_of_nonneg_right hpow hG)

theorem exists_actual_QLowBounds
    (G R Z : ℝ) (hG : 0 ≤ G) (hR : 0 ≤ R)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U S : Set Coord),
      SmoothPositiveOn g U → IsOpen U → ContDiffOn ℝ ∞ z U → S ⊆ U →
      (∀ p ∈ S, |p 0| ≤ R ∧ |p 1| ≤ R) →
      (∀ i j, CoordinateBound (fun p => g p i j) S 4 G) →
      CoordinateBound z S 3 Z →
      (∀ p ∈ S, d ≤ |(g p).det|) →
      (∀ p ∈ S, c ≤ |covHessian g z p 0 0|) →
      ∀ s0 speed : ℝ,
      (∀ p ∈ S, s0 ≤ heightQCoefficient g z 5 p) →
      (∀ p ∈ S, |heightQCoefficient g z 4 p| + Real.sqrt (heightQCoefficient g z 5 p) ≤ speed) →
      QLowBounds g z S s0 M speed := by
  obtain ⟨M, hM, hbound⟩ := exists_same_region_Q_low_bound_of_coordinate G R Z hG hR hd hc
  refine ⟨M, hM, ?_⟩
  intro g z U S hg hU hz hSU hcoords hgB hzB hdet hden s0 speed hs hspeed p hp
  have hb := hbound g z U S hg hU hz hSU hcoords hgB hzB hdet hden
  exact ⟨hs p hp, (hb 2 p hp).1, (hb 3 p hp).1, (hb 5 p hp).1,
    (hb 4 p hp).2 0, (hb 5 p hp).2 0, (hb 5 p hp).2 1, hspeed p hp⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QPositiveFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Flow

theorem actual_sheared_Q5_floor
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord} {G Z d M : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (q0 : ℝ) (hp : inverseShearCoordinates q0 p ∈ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hM : 0 < M)
    (hg0 : ∀ i j, |g (inverseShearCoordinates q0 p) i j| ≤ G)
    (hg1 : ∀ a i j, |coordPartial a (fun q => g q i j) (inverseShearCoordinates q0 p)| ≤ G)
    (hz1 : ∀ i, |coordPartial i z (inverseShearCoordinates q0 p)| ≤ Z)
    (hz2 : ∀ i j, |coordPartial i (coordPartial j z) (inverseShearCoordinates q0 p)| ≤ Z)
    (hdet : d ≤ |(g (inverseShearCoordinates q0 p)).det|)
    (hyy : 1 / M ≤ |covHessian g z (inverseShearCoordinates q0 p) 1 1|)
    (hD : (covHessian g z (inverseShearCoordinates q0 p)).det =
      gaussianCurvature g (inverseShearCoordinates q0 p) * heightEnergy g z (inverseShearCoordinates q0 p))
    (hxx : covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0)
    (hS : 0 < heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p) :
    shearedQPositiveFloor G Z d q0 M ≤
      heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p := by
  have hUS := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgS := metricInShearCoordinates_smoothPositive hg q0
  have hzS := heightInShearCoordinates_contDiffOn hz q0
  have hD' := darboux_in_shear_coordinates hg hz hU q0 hp hD
  have hQ := q_xx_coefficient_at_height hgS hUS hzS hp hxx hD'
  change heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p = _ at hQ
  have h11 := (covHessian_shear_entries hg hz hU q0 hp).1
  rw [hQ] at hS ⊢
  apply positive_negative_ratio_floor hM (shearedHessianUpper_pos q0 hG hZ hd) hxx hS
  · simpa only [h11] using hyy
  · exact sheared_Hxx_value_bound hg hU hz q0 hp hG hZ hd hg0 hg1 hz1 hz2 hdet

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_BoundedClassHyperbolicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation

theorem bounded_class_shear_estimates {g : MetricField} {z : Coord → ℝ}
    {M : ℕ} (h : BoundedAdmissibleHeight g M z) {kappa q0 : ℝ}
    (hkappa : 0 < kappa) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ modelSquare)
    (hK : gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2)
    (hq : |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * boundedClassWidth kappa M)) :
    (boundedClassSpeed kappa M) ^ 2 / 2 ≤ -shearTimeFactor g z q0 p ∧
    (boundedClassSpeed kappa M) ^ 2 / (2 * (M : ℝ)) ≤
      |covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0| ∧
    0 < qFirstCoefficient (metricInShearCoordinates g q0) 5
      (qSolutionJet (heightInShearCoordinates z q0) p) ∧
    |qFirstCoefficient (metricInShearCoordinates g q0) 4
      (qSolutionJet (heightInShearCoordinates z q0) p)| +
        Real.sqrt (qFirstCoefficient (metricInShearCoordinates g q0) 5
          (qSolutionJet (heightInShearCoordinates z q0) p)) < boundedClassWidth kappa M / 4 := by
  obtain ⟨hM, hadm, hjet, hHb, hEb⟩ := h
  obtain ⟨U, hU, hSU, hg, hz, hD, hE, hyy, hsmall⟩ := hadm
  have hMp : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hv := boundedClassSpeed_pos hkappa hM
  obtain ⟨hd, hxx, hS, hchar⟩ := actual_shear_hyperbolicity hg hz hU (hSU hp)
    hkappa (one_div_pos.mpr hMp) hv (boundedClassSpeed_sq_energy hkappa hM).le
    (hyy _ hp) (hHb _ hp).2 (hEb _ hp) hK hq (hD _ hp)
  have hdneg : shearTimeFactor g z q0 p < 0 := by
    have hv2 : 0 < (boundedClassSpeed kappa M) ^ 2 / 2 := half_pos (sq_pos_of_pos hv)
    linarith
  have hfac : covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 =
      shearTimeFactor g z q0 p * covHessian g z (inverseShearCoordinates q0 p) 1 1 :=
    sheared_Hxx_factor hg hz hU q0 (hSU hp) (hyy _ hp) (hD _ hp)
  refine ⟨hd, ?_, hS, hchar⟩
  calc
    _ = ((boundedClassSpeed kappa M) ^ 2 / 2) * (1 / (M : ℝ)) := by ring
    _ ≤ (-shearTimeFactor g z q0 p) * |covHessian g z (inverseShearCoordinates q0 p) 1 1| :=
      mul_le_mul hd (hHb _ hp).1 (one_div_nonneg.mpr hMp.le) (neg_pos.mpr hdneg).le
    _ = _ := by rw [hfac, abs_mul, abs_of_neg hdneg]

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_BoundedClassQFloor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem bounded_class_Q5_floor {g : MetricField} {z : Coord → ℝ}
    {M : ℕ} (h : BoundedAdmissibleHeight g M z) {kappa q0 G d : ℝ}
    (hkappa : 0 < kappa) (hG : 0 ≤ G) (hd : 0 < d) {p : Coord}
    (hp : inverseShearCoordinates q0 p ∈ modelSquare)
    (hgB : ∀ i j k, k ≤ 1 →
      ‖iteratedFDeriv ℝ k (fun r => g r i j) (inverseShearCoordinates q0 p)‖ ≤ G)
    (hdet : d ≤ |(g (inverseShearCoordinates q0 p)).det|)
    (hK : gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2)
    (hq : |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * boundedClassWidth kappa M)) :
    shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ) ≤
      heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p := by
  have hclass := h
  obtain ⟨hM, hadm, hjet, hHb, _⟩ := h
  obtain ⟨U, hU, hSU, hg, hz, hD, _, _, _⟩ := hadm
  have hMp : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  obtain ⟨_, hxxfloor, hS, _⟩ := bounded_class_shear_estimates hclass hkappa hp hK hq
  have hxx : covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
    intro he
    rw [he, abs_zero] at hxxfloor
    exact (not_le_of_gt (boundedClassShearHxxFloor_pos hkappa hM)) hxxfloor
  apply actual_sheared_Q5_floor hg hU hz q0 (hSU hp) hG hMp.le hd hMp
    ?_ ?_ ?_ ?_ hdet (hHb _ hp).1 (hD _ hp) hxx hS
  · intro i j
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hgB i j 0 (by omega)
  · intro a i j
    exact (norm_iteratedCoordPartial_le_jet (hg.1 i j) hU [a] (hSU hp)).trans
      (hgB i j 1 (by omega))
  · intro i
    exact (norm_iteratedCoordPartial_le_jet hz hU [i] (hSU hp)).trans
      (hjet 1 (by omega) _ hp)
  · intro i j
    exact (norm_iteratedCoordPartial_le_jet hz hU [i, j] (hSU hp)).trans
      (hjet 2 (by omega) _ hp)

theorem bounded_class_Q_principal_budgets {g : MetricField} {z : Coord → ℝ}
    {M : ℕ} (h : BoundedAdmissibleHeight g M z) {kappa q0 G d : ℝ}
    (hkappa : 0 < kappa) (hG : 0 ≤ G) (hd : 0 < d) {S : Set Coord}
    (hS : ∀ p ∈ S, inverseShearCoordinates q0 p ∈ modelSquare)
    (hgB : ∀ i j k, k ≤ 1 → ∀ p ∈ S,
      ‖iteratedFDeriv ℝ k (fun r => g r i j) (inverseShearCoordinates q0 p)‖ ≤ G)
    (hdet : ∀ p ∈ S, d ≤ |(g (inverseShearCoordinates q0 p)).det|)
    (hK : ∀ p ∈ S, gaussianCurvature g (inverseShearCoordinates q0 p) ≤ -kappa / 2)
    (hq : ∀ p ∈ S, |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * boundedClassWidth kappa M)) :
    0 < shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ) ∧
    ∀ p ∈ S,
      (boundedClassSpeed kappa M)^2 / (2 * (M : ℝ)) ≤
        |covHessian (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) p 0 0| ∧
      shearedQPositiveFloor G (M : ℝ) d q0 (M : ℝ) ≤
        heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p ∧
      |heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 4 p| +
        Real.sqrt (heightQCoefficient (metricInShearCoordinates g q0) (heightInShearCoordinates z q0) 5 p) ≤
          boundedClassWidth kappa M / 4 := by
  refine ⟨shearedQPositiveFloor_pos q0 hG (Nat.cast_nonneg M) hd (Nat.cast_pos.mpr h.1), ?_⟩
  intro p hp
  obtain ⟨_, hxx, _, hchar⟩ := bounded_class_shear_estimates h hkappa (hS p hp) (hK p hp) (hq p hp)
  exact ⟨hxx, bounded_class_Q5_floor h hkappa hG hd (hS p hp)
    (fun i j k hk => hgB i j k hk p hp) (hdet p hp) (hK p hp) (hq p hp), hchar.le⟩

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MixedDerivativeL2
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem principal_mixed_abs_le_fullP_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    |2 * hessianQuotient g z p| ≤
      ‖iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)‖ := by
  have h := (fderiv ℝ (sixVariableP g) (solutionJet z p)).le_opNorm
    (Pi.single 4 (1 : ℝ))
  simpa only [sixVariableP_mixed_axis_at_height hg hU hp hyy, Pi.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, norm_iteratedFDeriv_one] using h

theorem principal_yy_abs_le_fullP_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    |-((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p)| ≤
      ‖iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)‖ := by
  have h := (fderiv ℝ (sixVariableP g) (solutionJet z p)).le_opNorm
    (Pi.single 5 (1 : ℝ))
  simpa only [sixVariableP_yy_axis_at_height hg hU hp hyy, Pi.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, norm_iteratedFDeriv_one] using h

theorem ordered_mixed_eLpNorm_step
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hP : ∀ n ≤ N - 2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N - 3) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ N - 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (ds : List (Fin 2)) (hlen : ds.length = N) (hx : 2 ≤ ds.count 0) :
    ∃ es : List (Fin 2), es.length + 2 = N ∧
      (es ++ [0, 1]).count 0 < ds.count 0 ∧
      (es ++ [1, 1]).count 0 < ds.count 0 ∧
      eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤
        ‖C‖ₑ * eLpNorm (iteratedCoordPartial (es ++ [0, 1]) z) 2 (volume.restrict V) +
        ‖C‖ₑ * eLpNorm (iteratedCoordPartial (es ++ [1, 1]) z) 2 (volume.restrict V) +
        mixedRemainderL2Budget C B H V (N - 2) := by
  obtain ⟨es, hperm⟩ := word_two_x_permutation ds hx
  have heslen : es.length + 2 = N := by simpa [hlen] using hperm.length_eq.symm
  have hesN : es.length = N - 2 := by omega
  have hes : 5 ≤ es.length := by omega
  have hc := hperm.count_eq (0 : Fin 2)
  obtain ⟨_, _, hxy, hyyc⟩ := mixed_principal_word_orders es
  refine ⟨es, heslen, ?_, ?_, ?_⟩
  · simpa only [hc] using hxy
  · simpa only [hc] using hyyc
  let a : Coord → ℝ := fun p => 2 * hessianQuotient g z p
  let b : Coord → ℝ := fun p =>
    -((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p)
  let f : Coord → ℝ := iteratedCoordPartial (es ++ [0, 1]) z
  let h : Coord → ℝ := iteratedCoordPartial (es ++ [1, 1]) z
  let R : Coord → ℝ := mixedFaaRemainder g z (by omega) (coordinateDirections es)
  have haS : ContinuousOn a U :=
    continuousOn_const.mul (hessianQuotient_contDiffOn hg hU hz hyy).continuousOn
  have hbS : ContinuousOn b U :=
    (((hessianQuotient_contDiffOn hg hU hz hyy).continuousOn.pow 2).add
      ((gaussianCurvature_contDiffOn hg hU).continuousOn.mul
        (darbouxG_contDiffOn hg hU hz hyy).continuousOn)).neg
  have haf : AEStronglyMeasurable (fun p => a p * f p) (volume.restrict V) :=
    ((haS.mul (orderedPartial_contDiffOn hz hU (es ++ [0, 1])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hbh : AEStronglyMeasurable (fun p => b p * h p) (volume.restrict V) :=
    ((hbS.mul (orderedPartial_contDiffOn hz hU (es ++ [1, 1])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hafB : eLpNorm (fun p => a p * f p) 2 (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm f 2 (volume.restrict V) :=
    scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (fun p hp =>
      (principal_mixed_abs_le_fullP_one hg hU (hVU hp) (hyy p (hVU hp))).trans
        (hP 1 (by omega) p hp)) haf
  have hbhB : eLpNorm (fun p => b p * h p) 2 (volume.restrict V) ≤
      ‖C‖ₑ * eLpNorm h 2 (volume.restrict V) :=
    scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (fun p hp =>
      (principal_yy_abs_le_fullP_one hg hU (hVU hp) (hyy p (hVU hp))).trans
        (hP 1 (by omega) p hp)) hbh
  have hRB : eLpNorm R 2 (volume.restrict V) ≤ mixedRemainderL2Budget C B H V (N - 2) := by
    have hP' : ∀ n ≤ es.length, ∀ p ∈ V,
        ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C := by
      simpa only [hesN] using hP
    have hlo' : CoordinateBound z V (es.length - 1) B := by
      convert hlow using 1
      all_goals try with_reducible_and_instances rfl
      omega
    have hh' : ∀ fs : List (Fin 2), fs.length ≤ es.length + 1 →
        eLpNorm (iteratedCoordPartial fs z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) :=
      fun fs hfs => hheight fs (by omega)
    simpa only [hesN] using
      mixedFaaRemainder_eLpNorm_two hg hU hz hyy hV hVU es hes hC hB hP' hlo' hh'
  have he : iteratedCoordPartial ds z =ᵐ[volume.restrict V]
      (fun p => (a p * f p + b p * h p) + R p) := by
    filter_upwards [ae_restrict_mem hV] with p hp
    have he := (orderedPartial_perm hz hU hperm p (hVU hp)).trans
      (actualDarboux_ordered_mixed_elimination hg hU hz hD hyy (hVU hp) es (by omega))
    dsimp only [a, b, f, h, R]
    simpa only [neg_mul, sub_eq_add_neg] using he
  rw [eLpNorm_congr_ae he]
  have he1 := eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability)
    (f := fun point => a point * f point) (g := fun point => b point * h point)
    (μ := volume.restrict V) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he2 := eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by exact ((mixedFaaRemainder_continuousOn hg hU hz hyy (by omega) (coordinateDirections es)).mono hVU).aestronglyMeasurable hV)
    (f := fun point => a point * f point + b point * h point) (g := R)
    (μ := volume.restrict V) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact he2.trans (add_le_add (he1.trans (add_le_add hafB hbhB)) hRB)

theorem all_orderN_mixed_eLpNorm_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H Htop : ℝ≥0}
    (hP : ∀ n ≤ N - 2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N - 3) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ N - 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N - 1))) 2
      (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (ds : List (Fin 2)) (hlen : ds.length = N) :
    eLpNorm (iteratedCoordPartial ds z) 2 (volume.restrict V) ≤
      mixedXBudget C (mixedRemainderL2Budget C B H V (N - 2)) Htop N := by
  let R := mixedRemainderL2Budget C B H V (N - 2)
  have hind : ∀ j : ℕ, ∀ es : List (Fin 2), es.length = N → es.count 0 = j →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ mixedXBudget C R Htop j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro es hes hecount
      by_cases hj : j ≤ 1
      · exact (orderedPartial_at_most_one_x_eLpNorm hU hz hV hVU hv hxv es hes
          (by omega)).trans ((le_add_of_nonneg_right (by positivity)).trans
            (mixedXBudget_base_le C R Htop j))
      · obtain ⟨fs, hflen, hfc0, hfc1, hstep⟩ := ordered_mixed_eLpNorm_step
          hg hU hz hD hyy hV hVU hN hC hB hP hlow hheight es hes (by omega)
        have hlen0 : (fs ++ [0, 1]).length = N := by simpa using hflen
        have hlen1 : (fs ++ [1, 1]).length = N := by simpa using hflen
        have hb0 := ih ((fs ++ [0, 1]).count 0) (by omega) (fs ++ [0, 1]) hlen0 rfl
        have hb1 := ih ((fs ++ [1, 1]).count 0) (by omega) (fs ++ [1, 1]) hlen1 rfl
        have hb0' := hb0.trans (mixedXBudget_monotone C R Htop (by omega :
          (fs ++ [0, 1]).count 0 ≤ j - 1))
        have hb1' := hb1.trans (mixedXBudget_monotone C R Htop (by omega :
          (fs ++ [1, 1]).count 0 ≤ j - 1))
        have hsum := hstep.trans (mixedXBudget_step C R Htop (j - 1) hb0' hb1')
        simpa only [show j - 1 + 1 = j by omega] using hsum
  exact (hind (ds.count 0) ds hlen rfl).trans
    (mixedXBudget_monotone C R Htop (hlen ▸ List.count_le_length))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_RemainderAreaBudget
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Analytic

theorem coordinateL2Bound_order_step
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (hVS : V ⊆ modelSquare)
    {N : ℕ} (hN : 7 ≤ N) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H Htop : ℝ≥0}
    (hP : ∀ n ≤ N-2, ∀ p ∈ V,
      ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (N-3) B)
    (hheight : CoordinateL2Bound z V (N-1) H)
    (hv : eLpNorm (verticalJet z N) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞))
    (hxv : eLpNorm (coordPartial 0 (verticalJet z (N-1))) 2 (volume.restrict V) ≤ (Htop : ℝ≥0∞)) :
    CoordinateL2Bound z V N (uniformMixedOrderBudget C B H Htop N) := by
  have hmeas (word : List (Fin 2)) :
      AEStronglyMeasurable (iteratedCoordPartial word z) (volume.restrict V) :=
    ((orderedPartial_contDiffOn hz hU word).continuousOn.mono
      hVU).aestronglyMeasurable (μ := volume) hV
  intro ds hds
  rw [uniformMixedOrderBudget_coe]
  by_cases hloworder : ds.length ≤ N-1
  · exact (hheight ds hloworder).trans (le_max_left _ _)
  · have hlen : ds.length = N := by omega
    have hhigh := all_orderN_mixed_eLpNorm_two hg hU hz hD hyy hV hVU hN hC hB hP hlow
      (fun word hword => hheight.eLpNorm_le word hword (hmeas word)) hv hxv ds hlen
    rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num),
      ENNReal.toReal_ofNat] at hhigh
    exact (hhigh.trans (mixedXBudget_mono_remainder C
        (mixedRemainderL2Budget_mono_area C B H (measure_mono hVS) (N-2)) Htop N)).trans (le_max_right _ _)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapInductionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

variable {bStar : ℝ}

theorem exists_capInductionFlow
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => (g0+eta) q i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hh : CapInductionHeight (g0+eta) U Z c e0 z)
    (hk : 0 < kappa) (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) :
    ∃ (W : Set Coord) (Y : ℝ → ℝ → ℝ), CapInductionFlow (g0+eta) U G Z d c e0 kappa z Y W := by
  obtain ⟨V,Y,hV,hSV,hVU,hq,hqB,hchart,hY,hYs,hvar,hstart,hode,hrange,hdisp50,hdisp,himages,hcap⟩ :=
    exists_C8_one_flow_physical_cap_estimates hg hU hSU hh.smooth hG hZ hd hc he0 hgB hh.lowJet
      hdet hh.denominator hh.energy hh.quotient hh.darboux hk hbackground hsupport hcentral
  refine ⟨V, Y, hV, hSV, hVU, hq, hqB, hY, hYs, hstart, hode, hrange, hdisp, ?_⟩
  intro m bStar r
  exact ((hcap m).2 r.left r.right r.bottom r.top ((r.top+bStar)/2) r.left_gt r.right_lt r.bottom_gt
    r.horizontal r.vertical (by linarith [r.top_lt]) (by linarith [r.top_lt,r.ceiling_le])).2

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_BoundedClassSlabSmallness
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem bounded_class_quotient_change_from_origin
    {g : MetricField} {z : Coord → ℝ} {M : ℕ} (h : BoundedAdmissibleHeight g M z)
    {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun r => g r i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    {p : Coord} (hp : p ∈ modelSquare) :
    |hessianQuotient g z p - hessianQuotient g z 0| ≤
      boundedClassQuotientBudget G d M * (|p 0| + |p 1|) := by
  obtain ⟨hM, hadm, hjet, hHb, _⟩ := h
  obtain ⟨U, hU, hSU, hg, hz, _, _, _, _⟩ := hadm
  have hgCoord : ∀ i j, CoordinateBound (fun p => g p i j) modelSquare 4 G := by
    intro i j ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet (hg.1 i j) hU ds (hSU hp)).trans
      (hgB i j ds.length hds p hp)
  have hzCoord : CoordinateBound z modelSquare 5 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  obtain ⟨V, hV, hSV, _, _, hqV, hqB⟩ :=
    exists_open_quotient_domain_with_closed_low_bounds hg hU hSU hz hG (Nat.cast_nonneg M) hd
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hgCoord hzCoord hdet (fun p hp => (hHb p hp).1)
  apply quotient_change_from_origin hqV hV hSV (boundedClassQuotientBudget_nonneg hG hd hM) ?_ hp
  intro p hp i
  exact hqB [i] (by norm_num) p hp

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_BoundedClassCapRadius
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem bounded_class_slab_quotient_small_of_cap_radius
    {g : MetricField} {z : Coord → ℝ} {M : ℕ} (h : BoundedAdmissibleHeight g M z)
    {G d kappa q0 r : ℝ} (hG : 0 ≤ G) (hd : 0 < d) (hr : 0 ≤ r)
    (hq0 : |q0| ≤ 1 / 20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1 / (M : ℝ)) *
      (r + 107 * (boundedClassWidth kappa M * r) / 100) ≤ 9 / (100 * boundedClassWidth kappa M))
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => g a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hcenter : |hessianQuotient g z 0 - q0| ≤ 1 / (100 * boundedClassWidth kappa M))
    {p : Coord} (hp : inverseShearCoordinates q0 p ∈ modelSquare)
    (hx : |p 0| ≤ boundedClassWidth kappa M * r) (hy : |p 1| ≤ r) :
    |hessianQuotient g z (inverseShearCoordinates q0 p) - q0| ≤
      1 / (10 * boundedClassWidth kappa M) := by
  let L := boundedClassWidth kappa M
  let Q := boundedClassQuotientBudget G d M
  have hL : 0 < L := boundedClassWidth_pos kappa M
  have hQ : 0 ≤ Q := boundedClassQuotientBudget_nonneg hG hd h.1
  have hLr : 0 ≤ L * r := mul_nonneg hL.le hr
  have hdist := inverseShear_coordinate_sum_le (q0 := q0) hr hx hy
  have hdist' : |inverseShearCoordinates q0 p 0| + |inverseShearCoordinates q0 p 1| ≤
      r + 107 * (L * r) / 100 := by
    apply hdist.trans
    have hh := mul_le_mul_of_nonneg_right hq0 hLr
    nlinarith
  have hchange := bounded_class_quotient_change_from_origin h hG hd hgB hdet hp
  have hchange' : |hessianQuotient g z (inverseShearCoordinates q0 p) - hessianQuotient g z 0| ≤
      9 / (100 * L) := hchange.trans ((mul_le_mul_of_nonneg_left hdist' hQ).trans hrsmall)
  calc
    _ ≤ |hessianQuotient g z (inverseShearCoordinates q0 p) - hessianQuotient g z 0| +
        |hessianQuotient g z 0 - q0| := abs_sub_le _ _ _
    _ ≤ 9 / (100 * L) + 1 / (100 * L) := add_le_add hchange' hcenter
    _ = _ := by
      change 9 / (100 * L) + 1 / (100 * L) = 1 / (10 * L)
      field_simp [hL.ne']
      ring

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_LocalizedRemainderL2
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem exists_localized_actualHighRemainder_bound
    (G Z M : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hM : 0 ≤ M)
    {d c : ℝ} (hd : 0 < d) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : MetricField) (z : Coord → ℝ) (U V : Set Coord),
      SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
      (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
      (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
      ContDiffOn ℝ ∞ z U →
      (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) →
      (∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) →
      MeasurableSet V → V ⊆ modelSquare → volume V < (⊤ : ℝ≥0∞) →
      (∀ i j k, k ≤ m + 5 → ∀ p ∈ V,
        ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ M) →
      ∀ B : ℝ, 1 ≤ B → ∀ H : ℝ≥0,
      (∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
        ∀ p ∈ V, |heightStateFactor z n j p| ≤ B) →
      (∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
        eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) →
      eLpNorm (actualHighRemainder g z m) 2 (volume.restrict V) ≤
        actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m ∧
      actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m < (⊤ : ℝ≥0∞) ∧
      MemLp (actualHighRemainder g z m) 2 (volume.restrict V) := by
  obtain ⟨C, hC, houter⟩ := exists_same_region_remainder_outer_bound M Z hM hd hc m
  refine ⟨C, hC, ?_⟩
  intro g z U V hg hU hSU hgB hdet hz hzB hyy hV hVS hVfinite hgHigh B hB H hlow hheight
  have hgCoord (i j : Fin 2) : CoordinateBound (fun p => g p i j) modelSquare 4 G :=
    coordinateBound_of_frechet_bounds (hg.1 i j) hU hSU (hgB i j)
  have hzCoord : CoordinateBound z modelSquare 5 Z :=
    coordinateBound_five_of_frechet_eight hz hU hSU hzB
  obtain ⟨W, hW, hSW, hWU, hne, _, _, _, hfirst, _⟩ :=
    exists_open_low_height_coefficients hg hU hSU hz hG hZ hd hc hgCoord hzCoord hdet hyy
  have hgW : SmoothPositiveOn g W :=
    ⟨fun i j => (hg.1 i j).mono hWU, fun p hp => hg.2 p (hWU hp)⟩
  have hVW : V ⊆ W := hVS.trans hSW
  have hCfirst := heightPFirstBound_nonneg hG hZ hd hc
  have ho : ∀ w ∈ topResidualWords m, ∀ r, ∀ p ∈ V,
      |coordinateChainCoefficient g z w r p| ≤ C :=
    houter g z U V hg hU (hVS.trans hSU) hVS hgHigh
      ((hzCoord.mono (by norm_num) le_rfl).restrict_domain hVS)
      (fun p hp => hdet p (hVS hp)) (fun p hp => hyy p (hVS hp))
  have hf : ∀ i : Fin 2, ∀ p ∈ V,
      |coordPartial 1 (heightPFirst g z i) p| ≤ heightPFirstBound G Z d c :=
    fun i p hp => hfirst i [1] (by norm_num) p (hVS hp)
  exact ⟨actualHighRemainder_eLpNorm_two hgW hW (hz.mono hWU) hne hV hVW hm hC hCfirst hB
      hlow hheight ho hf,
    actualHighRemainderL2Budget_lt_top C (heightPFirstBound G Z d c) B H hVfinite m,
    actualHighRemainder_memLp_two hgW hW (hz.mono hWU) hne hV hVW hVfinite hm hC hCfirst hB
      hlow hheight ho hf⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_FiniteCapInduction
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

theorem uniform_finite_varying_lowerCap_L2
    (G Z d c e0 kappa : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    {bStar : ℝ} (J : CapMetricJetBudget bStar) :
    ∀ k : ℕ, ∀ r : LowerCapRectangle bStar,
      (∀ b ∈ lowerCapMetricRequests k r, 0 ≤ J b.1 b.2) → ∃ H : ℝ≥0,
      ∀ (g : MetricField) (U : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
        (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
        CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
        FiniteCapMetricJets g Y J (lowerCapMetricRequests k r) → CoordinateL2Bound z (r.image Y) (k+8) H := by
  intro k
  induction k with
  | zero =>
    intro r hJ
    refine ⟨originalC8L2Budget Z, ?_⟩
    intro g U z Y W hg hU hSU hgB hdet hh hf hlocal
    exact hh.original_L2 hU hSU hZ (hf.image_properties r).2.1 (hf.image_subset_square r)
  | succ k ih =>
    intro r hJ
    let T := r.energyOuter
    have hsourceRequest : (k+8,T) ∈ lowerCapMetricRequests (k+1) r := by
      simp [lowerCapMetricRequests,T]
    have hmixedRequest : (k+7,r) ∈ lowerCapMetricRequests (k+1) r := by
      simp [lowerCapMetricRequests]
    have htail : ∀ b, b ∈ lowerCapMetricRequests k T.expand →
        b ∈ lowerCapMetricRequests (k+1) r := by
      intro b hb
      change b ∈ (k+8,T)::(k+7,r)::lowerCapMetricRequests k T.expand
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hb)
    obtain ⟨H, hH⟩ := ih T.expand (fun b hb => hJ b (htail b hb))
    obtain ⟨CR, hCR0, hCR⟩ := exists_localized_actualHighRemainder_bound
      G Z (J (k+8) T) hG hZ (hJ (k+8,T) hsourceRequest) hd hc (k+5) (by omega)
    obtain ⟨CP, hCP0, hCP⟩ := exists_same_region_solution_P_jet_bound
      (J (k+7) r) Z (hJ (k+7,r) hmixedRequest) hd hc (k+7)
    let M := heightQuotientJetBound G Z d c
    let B := max 1 ((squareSobolevWeight (flowInteriorRadius M T.margin T.margin)+1)*(H : ℝ))
    have hB : 1 ≤ B := le_max_left _ _
    let Rraw := actualHighRemainderL2Budget CR (heightPFirstBound G Z d c) B H modelSquare (k+5)
    have hRfinite : Rraw < (⊤ : ℝ≥0∞) := actualHighRemainderL2Budget_lt_top CR
      (heightPFirstBound G Z d c) B H modelSquare_isCompact.measure_lt_top (k+5)
    let RB : ℝ≥0 := Rraw.toNNReal
    have hRB : (RB : ℝ≥0∞) = Rraw := ENNReal.coe_toNNReal hRfinite.ne
    let Ccap := lowerCapConstant G Z d c e0 kappa (k+8) r
    have hCcap : 0 < Ccap := lowerCapConstant_pos G Z d c e0 kappa (k+8) r
    let Htop : ℝ≥0 := ⟨Real.sqrt (Ccap*((RB : ℝ)^2+(H : ℝ)^2)), Real.sqrt_nonneg _⟩
    have hTopSq : (Htop : ℝ)^2 = Ccap*((RB : ℝ)^2+(H : ℝ)^2) :=
      Real.sq_sqrt (mul_nonneg hCcap.le (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    refine ⟨uniformMixedOrderBudget CP B H Htop (k+9), ?_⟩
    intro g U z Y W hg hU hSU hgB hdet hh hf hlocal
    have hlocalTail : FiniteCapMetricJets g Y J (lowerCapMetricRequests k T.expand) :=
      fun b hb => hlocal b (htail b hb)
    have hLarge : CoordinateL2Bound z (T.expand.image Y) (k+8) H := hH g U z Y W hg hU hSU hgB hdet hh hf hlocalTail
    have hT : CoordinateL2Bound z (T.image Y) (k+8) H :=
      hLarge.restrict (T.image_subset_expand Y)
    have hR : CoordinateL2Bound z (r.image Y) (k+8) H :=
      hT.restrict (r.image_subset_energyOuter Y)
    have hlowT0 : CoordinateBound z (T.image Y) (k+6)
        ((squareSobolevWeight (flowInteriorRadius M T.margin T.margin)+1)*(H : ℝ)) := by
      apply CapInductionFlow.pointwise_from_larger_L2 hh hf hG hZ hd hc T
      convert hLarge using 1
      all_goals try with_reducible_and_instances rfl
    have hlowT : CoordinateBound z (T.image Y) (k+6) B :=
      hlowT0.mono le_rfl (le_max_right _ _)
    obtain ⟨hTcompact, hTmeas, hTfinite, hTO⟩ := hf.image_properties T
    obtain ⟨hRcompact, hRmeas, hRfiniteImage, hRO⟩ := hf.image_properties r
    have hTS : T.image Y ⊆ modelSquare := hTO.trans modelOpenSquare_subset
    have hRS : r.image Y ⊆ modelSquare := hRO.trans modelOpenSquare_subset
    have hTU : T.image Y ⊆ U := hTS.trans hSU
    have hRU : r.image Y ⊆ U := hRS.trans hSU
    have hlowFactors : ∀ n j, n + heightStateBaseOrder j ≤ (k+5)+1 →
        ∀ p ∈ T.image Y, |heightStateFactor z n j p| ≤ B := by
      intro n j hn
      exact coordinateBound_heightFactors hlowT n j (by omega)
    have hL2Factors : ∀ n j, n + heightStateBaseOrder j ≤ (k+5)+3 →
        eLpNorm (heightStateFactor z n j) 2 (volume.restrict (T.image Y)) ≤ (H : ℝ≥0∞) := by
      intro n j hn
      exact hT.heightFactors_of_aestronglyMeasurable n j (by omega)
        (((heightStateFactor_contDiffOn hU hh.smooth n j).continuousOn.mono
          hTU).aestronglyMeasurable hTmeas)
    have hgHighT : ∀ i j n, n ≤ (k+5)+5 → ∀ p ∈ T.image Y,
        ‖iteratedFDeriv ℝ n (fun q => g q i j) p‖ ≤ J (k+8) T := by
      intro i j n hn p hp
      exact hlocal (k+8,T) hsourceRequest i j n (by omega) p hp
    obtain ⟨hsource, _, hsourceMem⟩ := hCR g z U (T.image Y) hg hU hSU hgB hdet
      hh.smooth hh.lowJet hh.denominator hTmeas hTS hTfinite hgHighT B hB H hlowFactors hL2Factors
    have hsourceRB : eLpNorm (actualHighRemainder g z (k+5)) 2
        (volume.restrict (T.image Y)) ≤ (RB : ℝ≥0∞) := by
      rw [hRB]
      exact hsource.trans (actualHighRemainderL2Budget_mono_area CR
        (heightPFirstBound G Z d c) B H (measure_mono hTS) (k+5))
    have hsourceIntegral : (∫ p in T.image Y, (actualHighRemainder g z (k+5) p)^2) ≤ (RB : ℝ)^2 :=
      integral_sq_le_of_eLpNorm_two_le hsourceMem hsourceRB
    have huIntegral : (∫ p in T.image Y, (verticalJet z (k+8) p)^2) ≤ (H : ℝ)^2 := by
      have hu := hT.integral_sq hh.smooth hU hTmeas hTU (List.replicate (k+8) 1) (by simp)
      simpa only [orderedPartial_replicate_y] using hu
    have hcap : (∫ p in r.image Y,
        (coordPartial 0 (verticalJet z (k+8)) p)^2+(verticalJet z (k+9) p)^2) ≤
        Ccap*((∫ p in T.image Y, (actualHighRemainder g z (k+5) p)^2)+
          (∫ p in T.image Y, (verticalJet z (k+8) p)^2)) := by
      simpa only [Nat.add_assoc, show 5+3=8 by omega, show 5+4=9 by omega] using hf.physicalEstimate (k+5) r
    have hgradient : (∫ p in r.image Y,
        (coordPartial 0 (verticalJet z (k+8)) p)^2+(verticalJet z (k+9) p)^2) ≤ (Htop : ℝ)^2 := by
      rw [hTopSq]
      exact hcap.trans (mul_le_mul_of_nonneg_left (add_le_add hsourceIntegral huIntegral) hCcap.le)
    have hxcont : ContinuousOn (coordPartial 0 (verticalJet z (k+8))) (r.image Y) :=
      ((partial_contDiffOn (verticalJet_contDiffOn hU hh.smooth (k+8)) hU 0).continuousOn).mono hRU
    have hycont : ContinuousOn (verticalJet z (k+9)) (r.image Y) :=
      (verticalJet_contDiffOn hU hh.smooth (k+9)).continuousOn.mono hRU
    have hparts := integral_each_sq_le_sum hRcompact hxcont hycont
    have hxTop : eLpNorm (coordPartial 0 (verticalJet z (k+8))) 2
        (volume.restrict (r.image Y)) ≤ (Htop : ℝ≥0∞) :=
      eLpNorm_two_le_of_integral_sq_le (compact_continuous_memLp_two hRcompact hxcont)
        (hparts.1.trans hgradient)
    have hyTop : eLpNorm (verticalJet z (k+9)) 2
        (volume.restrict (r.image Y)) ≤ (Htop : ℝ≥0∞) :=
      eLpNorm_two_le_of_integral_sq_le (compact_continuous_memLp_two hRcompact hycont)
        (hparts.2.trans hgradient)
    have hz2 : CoordinateBound z modelSquare 2 Z :=
      (coordinateBound_five_of_frechet_eight hh.smooth hU hSU hh.lowJet).mono (by norm_num) le_rfl
    have hP : ∀ n ≤ (k+9)-2, ∀ p ∈ r.image Y,
        ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ CP := by
      intro n hn p hp
      exact hCP g z U (r.image Y) hg hU hRU hRS
        (fun i j n hn p hp => hlocal (k+7,r) hmixedRequest i j n hn p hp)
        (hz2.restrict_domain hRS) (fun p hp => hdet p (hRS hp))
        (fun p hp => hh.denominator p (hRS hp)) n (by omega) p hp
    have hlowR : CoordinateBound z (r.image Y) ((k+9)-3) B := by
      intro word hword p hp
      exact hlowT word (by omega) p (r.image_subset_energyOuter Y hp)
    have hPrev : CoordinateL2Bound z (r.image Y) ((k+9)-1) H := by
      convert hR using 1
      all_goals try with_reducible_and_instances rfl
      omega
    have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
    have hgO : SmoothPositiveOn g modelOpenSquare :=
      ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
    have hDo : ∀ p ∈ modelOpenSquare,
        (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p :=
      fun p hp => hh.darboux p (modelOpenSquare_subset hp)
    have hyyO : ∀ p ∈ modelOpenSquare, covHessian g z p 1 1 ≠ 0 :=
      fun p hp => LowQuotient.denominator_ne_zero hc hh.denominator p (modelOpenSquare_subset hp)
    have hfinal := coordinateL2Bound_order_step hgO modelOpenSquare_isOpen (hh.smooth.mono hOU)
      hDo hyyO hRmeas hRO hRS (by omega : 7 ≤ k+9) hCP0 hB hP hlowR hPrev hyTop
      (by simpa only [show (k+9)-1=k+8 by omega] using hxTop)
    convert hfinal using 1
    all_goals try with_reducible_and_instances rfl

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_FiniteCapPointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

theorem uniform_finite_varying_lowerCap_pointwise
    (G Z d c e0 kappa : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    {bStar : ℝ} (J : CapMetricJetBudget bStar) (n : ℕ) (r : LowerCapRectangle bStar)
    (hJ : ∀ b ∈ lowerCapPointwiseRequests n r, 0 ≤ J b.1 b.2) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (U : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
        (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
        CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
        FiniteCapMetricJets g Y J (lowerCapPointwiseRequests n r) →
        CoordinateBound z (r.image Y) n B := by
  obtain ⟨H,hH⟩ := uniform_finite_varying_lowerCap_L2 G Z d c e0 kappa hG hZ hd hc
    J (n-6) r.expand hJ
  let M := heightQuotientJetBound G Z d c
  let B := (squareSobolevWeight (flowInteriorRadius M r.margin r.margin)+1)*(H : ℝ)
  have hr := flowInteriorRadius_pos M r.margin_pos r.margin_pos
  have hB : 0 ≤ B := by
    dsimp only [B,squareSobolevWeight]
    positivity
  refine ⟨B,hB,?_⟩
  intro g U z Y W hg hU hSU hgB hdet hh hf hlocal
  exact CapInductionFlow.pointwise_from_larger_L2 hh hf hG hZ hd hc r
    ((hH g U z Y W hg hU hSU hgB hdet hh hf hlocal).mono
      (by omega : n+2 ≤ (n-6)+8) le_rfl)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QMetricDensityDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem sixVariableQ_metric_density_difference
    {gTau gStar : MetricField} {U : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar U)
    (hU : IsOpen U) {w : DarbouxState} (hw : statePoint w ∈ U)
    (hxxTau : stateQDenominator gTau w ≠ 0) (hxxStar : stateQDenominator gStar w ≠ 0) :
    sixVariableQ gTau w-sixVariableQ gStar w =
      (curvatureDensity gTau (statePoint w)-curvatureDensity gStar (statePoint w))*
        qMetricDensityFactor gStar w+qMetricFirstError gTau gStar w := by
  rw [sixVariableQ_density_split hgTau hU hw hxxTau,
    sixVariableQ_density_split hgStar hU hw hxxStar]
  unfold qMetricFirstError
  ring

theorem actual_Q_metric_forcing_decomposition
    {gTau gStar : MetricField} {U : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar U)
    (hU : IsOpen U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U)
    (hxxTau : covHessian gTau z p 0 0 ≠ 0) (hxxStar : covHessian gStar z p 0 0 ≠ 0) :
    sixVariableQ gTau (qSolutionJet z p)-sixVariableQ gStar (qSolutionJet z p) =
      2*forcingCoefficient gStar z p*(curvatureDensity gTau p-curvatureDensity gStar p)+
        qMetricFirstError gTau gStar (qSolutionJet z p) := by
  rw [sixVariableQ_metric_density_difference hgTau hgStar hU
    (by simpa only [statePoint_qSolutionJet] using hp)
    (by simpa only [stateQDenominator_qSolutionJet] using hxxTau)
    (by simpa only [stateQDenominator_qSolutionJet] using hxxStar),
    statePoint_qSolutionJet,qMetricDensityFactor_at_height hgStar z hp hxxStar]
  ring

theorem actual_Q_metric_forcing_leading_identity
    {gTau gStar : MetricField} {U : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar U)
    (hU : IsOpen U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U)
    (hxxTau : covHessian gTau z p 0 0 ≠ 0) (hxxStar : covHessian gStar z p 0 0 ≠ 0)
    (leading : ℝ) :
    (sixVariableQ gTau (qSolutionJet z p)-sixVariableQ gStar (qSolutionJet z p))-
        2*forcingCoefficient gStar z p*leading =
      2*forcingCoefficient gStar z p*((curvatureDensity gTau p-curvatureDensity gStar p)-leading)+
        qMetricFirstError gTau gStar (qSolutionJet z p) := by
  rw [actual_Q_metric_forcing_decomposition hgTau hgStar hU z hp hxxTau hxxStar]
  ring

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Taylor
open SmoothLocal.Geometry SmoothLocal.HighEquation

theorem qResidual_contDiffOn {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) :
    ContDiffOn ℝ ∞ (qResidual g P) (comparisonDomain g U P I) := by
  have hs := spatialStrip_isOpen hI
  exact ((partial_contDiffOn (partial_contDiffOn hP hs 1) hs 1).mono
    (fun _ hp => hp.1)).sub
      ((sixVariableQ_contDiffOn hg hU).comp
        ((qSolutionJet_contDiffOn hs hP).mono (fun _ hp => hp.1)) (fun _ hp => hp.2))

theorem nextTaylorCoefficient_contDiffOn {g : MetricField} {U : Set Coord}
    {P : Coord → ℝ} {I : Set ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P (spatialStrip I)) (a : ℝ) (n : ℕ)
    (hcut : ∀ x ∈ I, (![x, a] : Coord) ∈ U)
    (hxx : ∀ x ∈ I, covHessian g P ![x, a] 0 0 ≠ 0) :
    ContDiffOn ℝ ∞ (nextTaylorCoefficient g a P n) I :=
  ((verticalJet_contDiffOn (comparisonDomain_isOpen hg hU hI hP)
    (qResidual_contDiffOn hg hU hI hP) n).comp (initialPoint_contDiff a).contDiffOn
      (fun x hx => mem_comparisonDomain hx (hcut x hx) (hxx x hx))).neg

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QCoefficientTube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qCoefficient_uniform_derivative_bound {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (M : ℝ) {c : ℝ} (hc : 0 < c) (i : Fin 6) (k : ℕ) :
    ∃ C : ℝ, ∀ w ∈ qCompactTube g S M c,
      ‖iteratedFDeriv ℝ k (qFirstCoefficient g i) w‖ ≤ C :=
  qCompactTube_derivative_bound hg hU hS hSU M hc (qFirstCoefficient_contDiffOn hg hU i) k

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QSegmentAveraging
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qCoefficient_segment_continuousOn {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) (i : Fin 6) :
    ContinuousOn (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma)) (Icc (0 : ℝ) 1) :=
  (qFirstCoefficient_contDiffOn hg hU i).continuousOn.comp
    (stateSegment_continuous w0 w1).continuousOn (fun t ht => hsegment t ht)

theorem sixVariableQ_segment_FTC {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) :
    sixVariableQ g w1 - sixVariableQ g w0 =
      ∑ i, averagedQCoefficient g w0 w1 i * (w1 i - w0 i) := by
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun sigma => sixVariableQ g (stateSegment w0 w1 sigma))
        (∑ i, qFirstCoefficient g i (stateSegment w0 w1 t) * (w1 i - w0 i)) t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hQ := ((sixVariableQ_contDiffOn hg hU).contDiffAt
      ((darbouxQStateDomain_isOpen hg hU).mem_nhds (hsegment t ht'))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hh := hQ.hasFDerivAt.comp_hasDerivAt t (stateSegment_hasDerivAt w0 w1 t)
    change HasDerivAt (fun sigma => sixVariableQ g (stateSegment w0 w1 sigma))
      (fderiv ℝ (sixVariableQ g) (stateSegment w0 w1 t) (w1 - w0)) t at hh
    rw [sixVariableQ_fderiv_apply] at hh
    exact hh
  have hi (i : Fin 6) : IntervalIntegrable
      (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
        volume (0 : ℝ) 1 :=
    ((qCoefficient_segment_continuousOn hg hU hsegment i).mul_const _).intervalIntegrable_of_Icc zero_le_one
  have hint : IntervalIntegrable
      (fun sigma => ∑ i, qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
        volume (0 : ℝ) 1 := by
    have hh := IntervalIntegrable.sum Finset.univ (fun i _ => hi i)
    change IntervalIntegrable
      (fun sigma => ∑ i, qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i))
      volume (0 : ℝ) 1 at hh
    exact hh
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [stateSegment_zero, stateSegment_one] at hFTC
  calc
    _ = ∫ sigma in (0 : ℝ)..1, ∑ i,
        qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i) := hFTC.symm
    _ = ∑ i, ∫ sigma in (0 : ℝ)..1,
        qFirstCoefficient g i (stateSegment w0 w1 sigma) * (w1 i - w0 i) :=
      intervalIntegral.integral_finsetSum (fun i _ => hi i)
    _ = _ := by simp only [intervalIntegral.integral_mul_const, averagedQCoefficient]

theorem averagedQCoefficient_lower {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U)
    (i : Fin 6) {gamma : ℝ}
    (hgamma : ∀ sigma ∈ Icc (0 : ℝ) 1, gamma ≤ qFirstCoefficient g i (stateSegment w0 w1 sigma)) :
    gamma ≤ averagedQCoefficient g w0 w1 i := by
  have hi : IntervalIntegrable
      (fun sigma => qFirstCoefficient g i (stateSegment w0 w1 sigma)) volume (0 : ℝ) 1 :=
    (qCoefficient_segment_continuousOn hg hU hsegment i).intervalIntegrable_of_Icc zero_le_one
  have hc : IntervalIntegrable (fun _ : ℝ => gamma) volume (0 : ℝ) 1 := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on zero_le_one hc hi hgamma
  simpa [averagedQCoefficient] using h

theorem averagedQPrincipal_margin {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w0 w1 : DarbouxState}
    (hsegment : ∀ sigma ∈ Icc (0 : ℝ) 1,
      stateSegment w0 w1 sigma ∈ darbouxQStateDomain g U) {gamma : ℝ}
    (hgamma : ∀ sigma ∈ Icc (0 : ℝ) 1,
      gamma ≤ qFirstCoefficient g 5 (stateSegment w0 w1 sigma)) :
    gamma ≤ averagedQCoefficient g w0 w1 5 ∧
      gamma ≤ (averagedQCoefficient g w0 w1 4 / 2) ^ 2 + averagedQCoefficient g w0 w1 5 := by
  have h := averagedQCoefficient_lower hg hU hsegment 5 hgamma
  exact ⟨h, by nlinarith [sq_nonneg (averagedQCoefficient g w0 w1 4 / 2)]⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QMetricJetTransfer
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem qFirstCoefficient_five_eq_numerator {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : w ∈ darbouxQStateDomain g U) :
    qFirstCoefficient g 5 w = -stateNumerator g w / (stateQDenominator g w)^2 := by
  unfold qFirstCoefficient
  rw [sixVariableQ_xx_axis hg hU hw]
  simp only [stateNumerator, jetNumerator, stateMixed, stateEnergy, div_pow]
  ring

theorem exists_uniform_Q_metric_state_margins (G W : ℝ)
    {d nu eta beta kappa : ℝ} (hG : 0 ≤ G) (hd : 0 < d)
    (hnu : 0 < nu) (heta : 0 < eta) (hbeta : 0 < beta) (hkappa : 0 < kappa) :
    ∃ epsilon A : ℝ, 0 < epsilon ∧ 1 ≤ A ∧
      ∀ (g g0 : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn g0 U → IsOpen U →
      ∀ w w0 : DarbouxState, statePoint w = statePoint w0 → statePoint w ∈ U →
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun p => g p i j) (statePoint w)‖ ≤ G) →
      (∀ i j k, k ≤ 2 → ‖iteratedFDeriv ℝ k (fun p => g0 p i j) (statePoint w)‖ ≤ G) →
      ‖w‖ ≤ W → ‖w0‖ ≤ W → d ≤ |(g (statePoint w)).det| → d ≤ |(g0 (statePoint w)).det| →
      (∀ i j k, k ≤ 2 →
        ‖iteratedFDeriv ℝ k (fun p => g0 p i j - g p i j) (statePoint w)‖ ≤ epsilon) →
      ‖w0 - w‖ ≤ epsilon → nu ≤ |stateQDenominator g w| → eta ≤ stateEnergy g w →
      stateNumerator g w ≤ -beta → gaussianCurvature g (statePoint w) ≤ -kappa →
      nu / 2 ≤ |stateQDenominator g0 w0| ∧ |stateQDenominator g0 w0| ≤ A ∧
      eta / 2 ≤ stateEnergy g0 w0 ∧
      (beta / 2) / A^2 ≤ qFirstCoefficient g0 5 w0 ∧
      ((kappa / 2) * (eta / 2)) / A^2 ≤
        (qFirstCoefficient g0 4 w0 / 2)^2 + qFirstCoefficient g0 5 w0 := by
  obtain ⟨epsilon, hepsilon, htransfer⟩ := universalQRaw_uniform_margins (max G W)
    hd hnu heta hbeta hkappa
  obtain ⟨A, hA, hAbound⟩ := universalQDenominator_uniform_bound (max G W) hd
  refine ⟨epsilon, A, hepsilon, hA, ?_⟩
  intro g g0 U hg hg0 hU w w0 hp hw hgB hg0B hwB hw0B hdet hdet0 hmetric hstate
    hden henergy hnum hK
  have hw0 : statePoint w0 ∈ U := by rw [← hp]; exact hw
  have ha := metricPBundle_mem_baseTube hg hU hw hG hgB hwB hdet
  have hb := metricPBundle_mem_baseTube hg0 hU hw0 hG
    (by simpa only [← hp] using hg0B) hw0B (by simpa only [← hp] using hdet0)
  have hab := metricPBundle_sub_norm_bound hg hg0 hU hp hw hepsilon.le hmetric hstate
  have hmargin := htransfer _ ha _ hb hab
    (by simpa only [universalQDenominator_metricPBundle] using hden)
    (by simpa only [universalEnergy_metricPBundle] using henergy)
    (by simpa only [universalQNumerator_metricPBundle hg hU hw] using hnum)
    (by simpa only [universalQCurvature_metricPBundle hg hU hw] using hK)
  have hd0 : nu / 2 ≤ |stateQDenominator g0 w0| := by
    simpa only [universalQDenominator_metricPBundle] using hmargin.1
  have hE0 : eta / 2 ≤ stateEnergy g0 w0 := by
    simpa only [universalEnergy_metricPBundle] using hmargin.2.1
  have hN0 : stateNumerator g0 w0 ≤ -(beta / 2) := by
    simpa only [universalQNumerator_metricPBundle hg0 hU hw0] using hmargin.2.2.1
  have hK0 : gaussianCurvature g0 (statePoint w0) ≤ -(kappa / 2) := by
    simpa only [universalQCurvature_metricPBundle hg0 hU hw0] using hmargin.2.2.2
  have hupper : |stateQDenominator g0 w0| ≤ A := by
    simpa only [universalQDenominator_metricPBundle] using hAbound _ hb
  have hne : stateQDenominator g0 w0 ≠ 0 :=
    abs_pos.mp ((half_pos hnu).trans_le hd0)
  have hdomain : w0 ∈ darbouxQStateDomain g0 U := ⟨hw0, hne⟩
  have hsq : (stateQDenominator g0 w0)^2 ≤ A^2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) ((by norm_num : (0 : ℝ) ≤ 1).trans hA)).mpr hupper
  refine ⟨hd0, hupper, hE0, ?_, ?_⟩
  · rw [qFirstCoefficient_five_eq_numerator hg0 hU hdomain]
    have hnumle : beta / 2 ≤ -stateNumerator g0 w0 := by
      simpa only [neg_neg] using neg_le_neg hN0
    exact div_le_div₀ ((half_pos hbeta).le.trans hnumle) hnumle (sq_pos_of_ne_zero hne) hsq
  · rw [q_principal_discriminant hg0 hU hdomain]
    have hk : kappa / 2 ≤ -gaussianCurvature g0 (statePoint w0) := by
      simpa only [neg_neg] using neg_le_neg hK0
    have hprod : (kappa / 2) * (eta / 2) ≤
        -(gaussianCurvature g0 (statePoint w0) * stateEnergy g0 w0) := by
      simpa only [neg_mul] using
        mul_le_mul hk hE0 (half_pos heta).le ((half_pos hkappa).le.trans hk)
    exact div_le_div₀
      ((mul_nonneg (half_pos hkappa).le (half_pos heta).le).trans hprod)
      hprod (sq_pos_of_ne_zero hne) hsq

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonEquation
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Taylor
open SmoothLocal.Weighted SmoothLocal.ODE SmoothLocal.Hyperbolic

theorem actual_comparison_mean_identity
    {g : MetricField} {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (P z : Coord → ℝ) (p : Coord)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) :
    sixVariableQ g (qSolutionJet z p)-sixVariableQ g (qSolutionJet P p) =
      comparisonCoefficient g P z 2 p*(coordPartial 0 z p-coordPartial 0 P p)+
      comparisonCoefficient g P z 3 p*(coordPartial 1 z p-coordPartial 1 P p)+
      comparisonCoefficient g P z 4 p*(coordPartial 0 (coordPartial 1 z) p-
        coordPartial 0 (coordPartial 1 P) p)+
      comparisonCoefficient g P z 5 p*(coordPartial 0 (coordPartial 0 z) p-
        coordPartial 0 (coordPartial 0 P) p) := by
  have hh := sixVariableQ_segment_FTC hg hU hseg
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  simp [comparisonCoefficient,Fin.sum_univ_succ,qSolutionJet]
  ring

theorem comparison_equation_from_darboux
    {g g0 : MetricField} {U : Set Coord} {P z : Coord → ℝ}
    (hg : SmoothPositiveOn g U) (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p)
    (hxx : covHessian g z p 0 0 ≠ 0)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g0 U) :
    hyperbolicOperator (comparisonCoefficient g0 P z 4) (comparisonCoefficient g0 P z 5)
      (comparisonDifference P z) p =
        comparisonCoefficient g0 P z 3 p*coordPartial 1 (comparisonDifference P z) p+
        comparisonCoefficient g0 P z 2 p*coordPartial 0 (comparisonDifference P z) p+
        (sixVariableQ g (qSolutionJet z p)-sixVariableQ g0 (qSolutionJet z p)-qResidual g0 P p) := by
  have hQ := (darbouxDet_iff_sixVariableQ hg hU hz hp hxx).mp hD
  have hmean := actual_comparison_mean_identity hg0 hU P z p hseg
  have hsub (ds : List (Fin 2)) := CoordinateBound.iterated_sub hz hP hU ds hp
  have h0 : coordPartial 0 (comparisonDifference P z) p = coordPartial 0 z p-coordPartial 0 P p := hsub [0]
  have h1 : coordPartial 1 (comparisonDifference P z) p = coordPartial 1 z p-coordPartial 1 P p := hsub [1]
  have h00 : coordPartial 0 (coordPartial 0 (comparisonDifference P z)) p =
      coordPartial 0 (coordPartial 0 z) p-coordPartial 0 (coordPartial 0 P) p := hsub [0,0]
  have h01 : coordPartial 0 (coordPartial 1 (comparisonDifference P z)) p =
      coordPartial 0 (coordPartial 1 z) p-coordPartial 0 (coordPartial 1 P) p := hsub [0,1]
  have h11 : coordPartial 1 (coordPartial 1 (comparisonDifference P z)) p =
      coordPartial 1 (coordPartial 1 z) p-coordPartial 1 (coordPartial 1 P) p := hsub [1,1]
  unfold hyperbolicOperator qResidual
  rw [h0,h1,h00,h01,h11,hQ]
  linarith

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonCoefficientSmooth
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
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem comparisonIntegrand_contDiffOn {g : MetricField} {P z : Coord → ℝ}
    {U : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (comparisonIntegrand g P z i) (comparisonParameterDomain g P z U) :=
  (qFirstCoefficient_contDiffOn hg hU i).comp
    ((comparisonStateMap_contDiffOn hU hP hz).mono inter_subset_left) (fun _ hq => hq.2)

theorem comparisonCoefficient_contDiffOn {g : MetricField} {P z : Coord → ℝ}
    {U W : Set Coord} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hW : IsOpen W) (hWU : W ⊆ U)
    (hsegment : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) (i : Fin 6) :
    ContDiffOn ℝ ∞ (comparisonCoefficient g P z i) W := by
  rw [comparisonCoefficient_eq_parameterIntegral]
  apply compactParameterIntegral_contDiffOn (comparisonIntegrand_contDiffOn hg hU hP hz i)
    (comparisonParameterDomain_isOpen hg hU hP hz) hW
  intro q hq
  exact ⟨⟨hWU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩

theorem exists_comparison_coefficient_neighborhood
    {g : MetricField} {P z : Coord → ℝ} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hS : IsCompact S) (hSU : S ⊆ U)
    (hsegment : ∀ p ∈ S, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) :
    ∃ W : Set Coord, IsOpen W ∧ S ⊆ W ∧ W ⊆ U ∧
      (∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
        qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U) ∧
      ∀ i : Fin 6, ContDiffOn ℝ ∞ (comparisonCoefficient g P z i) W := by
  have hprod : S ×ˢ Icc (0 : ℝ) 1 ⊆ comparisonParameterDomain g P z U := by
    intro q hq
    exact ⟨⟨hSU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩
  obtain ⟨W,J,hW,_,hSW,hIJ,hWJ⟩ := generalized_tube_lemma hS isCompact_Icc
    (comparisonParameterDomain_isOpen hg hU hP hz) hprod
  have hWU : W ⊆ U := by
    intro p hp
    have hj : (0 : ℝ) ∈ J := hIJ (by norm_num)
    exact (hWJ (show (p, (0 : ℝ)) ∈ W ×ˢ J from ⟨hp,hj⟩)).1.1
  have hseg : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U := by
    intro p hp sigma hs
    exact (hWJ (show (p, sigma) ∈ W ×ˢ J from ⟨hp,hIJ hs⟩)).2
  exact ⟨W,hW,hSW,hWU,hseg,fun i => comparisonCoefficient_contDiffOn hg hU hP hz hW hWU hseg i⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ActualComparisonTestCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.Weighted SmoothLocal.Hyperbolic SmoothLocal.Taylor

theorem actual_comparison_tested_source {g gRef : MetricField} {P z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U) {p : Coord} (hp : p ∈ U)
    (hD : (covHessian g z p).det=gaussianCurvature g p*heightEnergy g z p)
    (hxx : covHessian g z p 0 0 ≠ 0)
    (hseg : ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef U) :
    sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p =
      testedOperatorSource (comparisonCoefficient gRef P z 4) (comparisonCoefficient gRef P z 5)
        (comparisonCoefficient gRef P z 3) (comparisonCoefficient gRef P z 2) (comparisonDifference P z) p := by
  have hh := comparison_equation_from_darboux hg hgRef hU hz hP hp hD hxx hseg
  unfold testedOperatorSource
  linarith

theorem actual_comparison_source_test_cost {a delta tau K K1 M B : ℝ} {N : ℕ}
    {g gRef : MetricField} {P z : Coord → ℝ} {U : Set Coord}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 1 ≤ tau)
    (hK : 0 ≤ K) (hK1 : 0 ≤ K1) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hg : SmoothPositiveOn g U) (hgRef : SmoothPositiveOn gRef U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U) (hP : ContDiffOn ℝ ∞ P U) (hSU : pulseStrip a delta tau ⊆ U)
    (hD : ∀ p ∈ pulseStrip a delta tau,
      (covHessian g z p).det=gaussianCurvature g p*heightEnergy g z p)
    (hxx : ∀ p ∈ pulseStrip a delta tau, covHessian g z p 0 0 ≠ 0)
    (hseg : ∀ p ∈ pulseStrip a delta tau, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain gRef U)
    (hcoeff : ∀ i : Fin 6, ∀ p ∈ pulseStrip a delta tau, |comparisonCoefficient gRef P z i p| ≤ K)
    (hderiv : ∀ i : Fin 6, ∀ p ∈ pulseStrip a delta tau,
      |coordPartial 0 (comparisonCoefficient gRef P z i) p| ≤ K1)
    (hL2 : ∀ theta ∈ Icc (-(delta/tau)) (delta/tau), ∀ i : Fin 2,
      Real.sqrt (∫ x in Icc (-a) a, (coordPartial i (comparisonDifference P z) (boxPoint x theta))^2) ≤
        M*delta*tau/tau^N)
    (hinitial : ∀ x ∈ Icc (-a) a,
      coordPartial 1 (comparisonDifference P z) (boxPoint x (-(delta/tau)))=0)
    (hjet : ∀ k ≤ N, ∀ x ∈ Icc (-a) a,
      ‖iteratedFDeriv ℝ k (heightCauchyVelocity (comparisonDifference P z) (delta/tau)) x‖ ≤ B) :
    |pulseWeightedMoment a delta tau
      (fun p => sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p)| ≤
      ((2*a)*cutoffEdgeDerivativeBound a ha N B)/tau^N+
      (4*pulseTestDerivativeBound a ha*K*Real.sqrt (2*a)*M)*delta^2*tau/tau^N+
      (4*axisBumpDerivativeBound a ha 0*(K1+K)*Real.sqrt (2*a)*M)*delta^2/tau^N := by
  have htpos := zero_lt_one.trans_le ht
  have hab : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd htpos.le]
  obtain ⟨W,hW,hSW,hWU,_,hcoeffSmooth⟩ := exists_comparison_coefficient_neighborhood
    hgRef hU hP hz (closedRectangle_compact _ _ _ _) hSU hseg
  obtain ⟨radius,lo,hi,hRad,hlo,hhi,hRect⟩ := exists_containing_coordinateRectangle hW ha hab hSW
  have hI : IsOpen (Ioo (-radius) radius) := isOpen_Ioo
  have hsub : Icc (-a) a ⊆ Ioo (-radius) radius := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hupper (x : ℝ) (hx : x ∈ Ioo (-radius) radius) : (![x,delta/tau] : Coord) ∈ W := by
    apply hRect
    exact ⟨hx,⟨hlo.trans_le hab,hhi⟩⟩
  have hv : ContDiffOn ℝ ∞ (comparisonDifference P z) W := (hz.sub hP).mono hWU
  have hcost := testedOperatorSource_moment_cost ha hd ht hK hK1 hM hB
    (hcoeffSmooth 4) (hcoeffSmooth 5) (hcoeffSmooth 3) (hcoeffSmooth 2) hv hW hSW
    (fun p hp => ⟨hcoeff 4 p hp,hcoeff 5 p hp,hcoeff 3 p hp,hcoeff 2 p hp⟩)
    (fun p hp => ⟨hderiv 4 p hp,hderiv 5 p hp⟩) hL2 hI hsub hupper hinitial hjet
  have heq : pulseWeightedMoment a delta tau
      (fun p => sixVariableQ g (qSolutionJet z p)-sixVariableQ gRef (qSolutionJet z p)-qResidual gRef P p) =
      pulseWeightedMoment a delta tau
        (testedOperatorSource (comparisonCoefficient gRef P z 4) (comparisonCoefficient gRef P z 5)
          (comparisonCoefficient gRef P z 3) (comparisonCoefficient gRef P z 2) (comparisonDifference P z)) := by
    apply setIntegral_congr_fun (pulsePairRectangle_isCompact a delta tau).measurableSet
    intro q hq
    dsimp only [Pi.sub_apply,Pi.mul_apply]
    rw [actual_comparison_tested_source hg hgRef hU hz hP (hSU (pulsePairPoint_mem hq))
      (hD _ (pulsePairPoint_mem hq)) (hxx _ (pulsePairPoint_mem hq)) (hseg _ (pulsePairPoint_mem hq))]
  rw [heq]
  exact hcost

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonCoefficientDerivative
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
open SmoothLocal.Geometry SmoothLocal.Analytic

theorem comparisonIntegrand_parameter_partial
    {g : MetricField} {P z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    {p : Coord} {sigma : ℝ} (hp : p ∈ U)
    (hsegment : qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U)
    (i : Fin 6) (j : Fin 2) :
    compactParameterPartial (comparisonIntegrand g P z i) (p,sigma) (Pi.single j 1) =
      fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
        ((1-sigma) • coordPartial j (qSolutionJet P) p +
          sigma • coordPartial j (qSolutionJet z) p) := by
  have hJP := ((qSolutionJet_contDiffOn hU hP).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hJz := ((qSolutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hQ := ((qFirstCoefficient_contDiffOn hg hU i).contDiffAt
    ((darbouxQStateDomain_isOpen hg hU).mem_nhds hsegment)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hstate : HasFDerivAt (fun x => qHeightJetSegment P z sigma x)
      ((1-sigma) • fderiv ℝ (qSolutionJet P) p + sigma • fderiv ℝ (qSolutionJet z) p) p :=
    (hJP.hasFDerivAt.const_smul (1-sigma)).add (hJz.hasFDerivAt.const_smul sigma)
  have hchain := hQ.hasFDerivAt.comp p hstate
  have hparam := compactParameter_slice_hasFDerivAt
    ((comparisonIntegrand_contDiffOn hg hU hP hz i).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (comparisonParameterDomain_isOpen hg hU hP hz)
    (show (p,sigma) ∈ comparisonParameterDomain g P z U from
      ⟨⟨hp,mem_univ _⟩,hsegment⟩)
  have he := hparam.unique hchain
  simpa only [ContinuousLinearMap.comp_apply,add_apply,
    smul_apply,coordPartial] using
      congrArg (fun A : Coord →L[ℝ] ℝ => A (Pi.single j 1)) he

theorem comparisonCoefficient_partial
    {g : MetricField} {P z : Coord → ℝ} {U W : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (hW : IsOpen W) (hWU : W ⊆ U)
    (hsegment : ∀ p ∈ W, ∀ sigma ∈ Icc (0 : ℝ) 1,
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g U)
    {p : Coord} (hp : p ∈ W) (i : Fin 6) (j : Fin 2) :
    coordPartial j (comparisonCoefficient g P z i) p =
      ∫ sigma in (0 : ℝ)..1,
        fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
          ((1-sigma) • coordPartial j (qSolutionJet P) p +
            sigma • coordPartial j (qSolutionJet z) p) := by
  rw [comparisonCoefficient_eq_parameterIntegral]
  have hUD : W ×ˢ Icc (0 : ℝ) 1 ⊆ comparisonParameterDomain g P z U := by
    intro q hq
    exact ⟨⟨hWU hq.1,mem_univ _⟩,hsegment q.1 hq.1 q.2 hq.2⟩
  rw [compactParameterIntegral_coordPartial (comparisonIntegrand_contDiffOn hg hU hP hz i)
    (comparisonParameterDomain_isOpen hg hU hP hz) hW hUD hp j,
    intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro sigma hs
  exact comparisonIntegrand_parameter_partial hg hU hP hz (hWU hp) (hsegment p hp sigma hs) i j

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonCoefficientBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem exists_uniform_comparison_coefficient_bounds
    {g : MetricField} {U S : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (R Z0 Z : ℝ) (hR : 0 ≤ R) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P z : Coord → ℝ) (V T : Set Coord),
      IsOpen V → V ⊆ U → ContDiffOn ℝ ∞ P V → ContDiffOn ℝ ∞ z V → T ⊆ S → T ⊆ V →
      (∀ p ∈ T, ‖p‖ ≤ R) → CoordinateBound P T 3 Z0 → CoordinateBound z T 3 Z →
      (∀ p ∈ T, ∀ sigma ∈ Icc (0 : ℝ) 1,
        c ≤ |stateQDenominator g (qHeightJetSegment P z sigma p)|) →
      ∀ i : Fin 6, ∀ p ∈ T,
        |comparisonCoefficient g P z i p| ≤ C ∧
        ∀ j : Fin 2, |coordPartial j (comparisonCoefficient g P z i) p| ≤
          C*(max 1 Z0+max 1 Z) := by
  classical
  let A := max R (max Z0 Z)
  choose C0 hC0 using fun i : Fin 6 => qCoefficient_uniform_derivative_bound hg hU hS hSU A hc i 0
  choose C1 hC1 using fun i : Fin 6 => qCoefficient_uniform_derivative_bound hg hU hS hSU A hc i 1
  let C := 1 + ∑ i : Fin 6, (max 0 (C0 i)+max 0 (C1 i))
  have hnon (i : Fin 6) : 0 ≤ max 0 (C0 i)+max 0 (C1 i) := by positivity
  have hCle : 1 ≤ C := by
    have hs : 0 ≤ ∑ i : Fin 6, (max 0 (C0 i)+max 0 (C1 i)) :=
      Finset.sum_nonneg (fun i _ => hnon i)
    dsimp [C]
    linarith
  have hC0le (i : Fin 6) : C0 i ≤ C := by
    have hi := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    dsimp [C]
    linarith [le_max_right 0 (C0 i),le_max_left 0 (C1 i)]
  have hC1le (i : Fin 6) : C1 i ≤ C := by
    have hi := Finset.single_le_sum (fun j _ => hnon j) (Finset.mem_univ i)
    dsimp [C]
    linarith [le_max_right 0 (C1 i),le_max_left 0 (C0 i)]
  refine ⟨C,hCle,?_⟩
  intro P z V T hV hVU hP hz hTS hTV hpB hPZ hzZ hfloor i p hp
  have hgV : SmoothPositiveOn g V := hg.mono hVU
  have h0 : ‖qSolutionJet P p‖ ≤ A :=
    (qSolutionJet_norm_bound_of_words hR (hpB p hp)
      (fun ds hds => hPZ ds (by omega) p hp)).trans
      (max_le_max le_rfl (le_max_left _ _))
  have h1 : ‖qSolutionJet z p‖ ≤ A :=
    (qSolutionJet_norm_bound_of_words hR (hpB p hp)
      (fun ds hds => hzZ ds (by omega) p hp)).trans
      (max_le_max le_rfl (le_max_right _ _))
  have htube (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P z sigma p ∈ qCompactTube g S A c := by
    refine ⟨⟨?_,?_⟩,hfloor p hp sigma hs⟩
    · change statePoint (qHeightJetSegment P z sigma p) ∈ S
      rw [statePoint_qHeightJetSegment]
      exact hTS hp
    · have hb := stateSegment_coord_bound hs
        (fun j => (norm_le_pi_norm (qSolutionJet P p) j).trans h0)
        (fun j => (norm_le_pi_norm (qSolutionJet z p) j).trans h1)
      exact ⟨fun j => (abs_le.mp (hb j)).1,fun j => (abs_le.mp (hb j)).2⟩
  have hseg (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      qHeightJetSegment P z sigma p ∈ darbouxQStateDomain g V := by
    have hd := qCompactTube_subset_domain hSU A hc (htube sigma hs)
    exact ⟨by simpa only [statePoint_qHeightJetSegment] using hTV hp,hd.2⟩
  have hval (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      |qFirstCoefficient g i (qHeightJetSegment P z sigma p)| ≤ C := by
    have hb := (hC0 i _ (htube sigma hs)).trans (hC0le i)
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb
  have hder (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :
      ‖fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_one] using (hC1 i _ (htube sigma hs)).trans (hC1le i)
  constructor
  · change ‖∫ sigma in (0 : ℝ)..1,
        qFirstCoefficient g i (qHeightJetSegment P z sigma p)‖ ≤ C
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C)
      (f := fun sigma => qFirstCoefficient g i (qHeightJetSegment P z sigma p)) (by
        intro sigma hs
        have hs0 : sigma ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
        exact hval sigma ⟨hs0.1.le,hs0.2⟩)
    simpa only [sub_zero,abs_one,mul_one] using hb
  · intro j
    obtain ⟨W,hW,hpW,hWU,hWseg,_⟩ := exists_comparison_coefficient_neighborhood
      hgV hV hP hz isCompact_singleton (singleton_subset_iff.mpr (hTV hp))
      (fun _ hq sigma hs => by simpa only [mem_singleton_iff.mp hq] using hseg sigma hs)
    rw [comparisonCoefficient_partial hgV hV hP hz hW hWU hWseg (hpW (mem_singleton p)) i j,
      ← Real.norm_eq_abs]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C*(max 1 Z0+max 1 Z)) (f := fun sigma =>
        fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)
          ((1-sigma) • coordPartial j (qSolutionJet P) p+sigma • coordPartial j (qSolutionJet z) p)) ?_
    · simpa only [sub_zero,abs_one,mul_one] using hb
    intro sigma hs
    have hs' : sigma ∈ Icc (0 : ℝ) 1 := by
      have hs0 : sigma ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hs
      exact ⟨hs0.1.le,hs0.2⟩
    exact ((fderiv ℝ (qFirstCoefficient g i) (qHeightJetSegment P z sigma p)).le_opNorm _).trans
      (mul_le_mul (hder sigma hs')
        (comparison_segment_direction_bound hV hP hz hTV hPZ hzZ hp hs' j)
        (norm_nonneg _) (zero_le_one.trans hCle))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ActualCentralShearMargins
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow

theorem actual_central_sheared_solution_margins
    {g0 : MetricField} {kappa q0 r G d : ℝ} {M : ℕ}
    (eta : metricPatchSet g0 kappa) {z : Coord → ℝ}
    (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z)
    (hG : 0 ≤ G) (hd : 0 < d) (hkappa : 0 < kappa) (hr : 0 ≤ r)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hcenter : |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
      1/(100*boundedClassWidth kappa M))
    {p : Coord} (hx : |p 0| ≤ boundedClassWidth kappa M*r) (ht : |p 1| ≤ r) :
    let g := metricInShearCoordinates (perturbedMetric g0 eta.val) q0
    let zs := heightInShearCoordinates z q0
    inverseShearCoordinates q0 p ∈ modelSquare ∧
      (boundedClassSpeed kappa M)^2/(2*(M : ℝ)) ≤ |covHessian g zs p 0 0| ∧
      1/(M : ℝ) ≤ |covHessian g zs p 1 1| ∧
      1/(M : ℝ) ≤ heightEnergy g zs p ∧
      gaussianCurvature g p ≤ -(kappa/2) ∧
      (covHessian g zs p).det = gaussianCurvature g p*heightEnergy g zs p ∧
      (hessianQuotient g zs p)^2+gaussianCurvature g p*darbouxG g zs p < 0 := by
  dsimp only
  have hpC := inverseShear_slab_mem_centralBox
    ((by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M))
    hr hLr hq0 hx ht
  have hpS := centralBox_subset_modelSquare hpC
  have hq := bounded_class_slab_quotient_small_of_cap_radius hclass hG hd hr hq0 hrsmall
    hgB hdet hcenter hpS hx ht
  have hK : gaussianCurvature (perturbedMetric g0 eta.val) (inverseShearCoordinates q0 p) ≤ -kappa/2 :=
    (eta.property.2 _ hpC).le
  have hgeom := bounded_class_shear_estimates hclass hkappa hpS hK hq
  obtain ⟨hM,hadm,_,hHb,hEb⟩ := hclass
  obtain ⟨U,hU,hSU,hg,hz,hD,_,hyy,_⟩ := hadm
  have hpU := hSU hpS
  have h11 := (covHessian_shear_entries hg hz hU q0 hpU).1
  have hEnergy := heightEnergy_in_shear_coordinates (g := perturbedMetric g0 eta.val) hz hU q0 hpU
  have hCurvature := gaussianCurvature_in_shear_coordinates hg hU q0 hpU
  have hqShear := hessianQuotient_in_shear_coordinates hg hz hU q0 hpU (hyy _ hpS)
  have htimeeq :
      (hessianQuotient (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
        (heightInShearCoordinates z q0) p)^2+
        gaussianCurvature (metricInShearCoordinates (perturbedMetric g0 eta.val) q0) p*
          darbouxG (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
            (heightInShearCoordinates z q0) p =
        shearTimeFactor (perturbedMetric g0 eta.val) z q0 p := by
    unfold shearTimeFactor darbouxG
    rw [hqShear,hCurvature,hEnergy,h11]
  have htime : shearTimeFactor (perturbedMetric g0 eta.val) z q0 p < 0 := by
    have hv2 := half_pos (sq_pos_of_pos (boundedClassSpeed_pos hkappa hM))
    linarith [hgeom.1]
  refine ⟨hpS,hgeom.2.1,?_,?_,?_,darboux_in_shear_coordinates hg hz hU q0 hpU (hD _ hpS),?_⟩
  · rw [h11]
    exact (hHb _ hpS).1
  · rw [hEnergy]
    exact hEb _ hpS
  · rw [hCurvature]
    simpa only [neg_div] using hK
  · rw [htimeeq]
    exact htime

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_ActualPatchQRectangle
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry SmoothLocal.Pulse SmoothLocal.HighEquation SmoothLocal.Flow
open SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Hyperbolic

theorem actual_patch_closed_strip_Hxx_floor
    {g0 : MetricField} {kappa q0 r b G d : ℝ} {M : ℕ}
    (eta : metricPatchSet g0 kappa)
    {z : Coord → ℝ} (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z)
    (hG : 0 ≤ G) (hd : 0 < d) (hkappa : 0 < kappa) (hr : 0 ≤ r) (hb : b ≤ 0)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hcenter : |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
      1/(100*boundedClassWidth kappa M))
    {p : Coord} (hp : p ∈ closedRectangle (-(boundedClassWidth kappa M*r))
      (boundedClassWidth kappa M*r) (-r) b) :
    inverseShearCoordinates q0 p ∈ modelOpenSquare ∧
      (boundedClassSpeed kappa M)^2/(2*(M : ℝ)) ≤
        |covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
          (heightInShearCoordinates z q0) p 0 0| := by
  have hx : |p 0| ≤ boundedClassWidth kappa M*r := abs_le.mpr hp.1
  have hy : |p 1| ≤ r := abs_le.mpr ⟨hp.2.1,(hp.2.2.trans hb).trans hr⟩
  have hpC := inverseShear_slab_mem_centralBox
    ((by norm_num : (1 : ℝ) ≤ 100).trans (boundedClassWidth_ge_hundred kappa M))
    hr hLr hq0 hx hy
  have hpS := centralBox_subset_modelSquare hpC
  have hq := bounded_class_slab_quotient_small_of_cap_radius hclass hG hd hr hq0 hrsmall
    hgB hdet hcenter hpS hx hy
  have hgeom := bounded_class_shear_estimates hclass hkappa hpS (eta.property.2 _ hpC).le hq
  exact ⟨centralBox_subset_modelOpenSquare hpC,hgeom.2.1⟩

theorem exists_actual_patch_Q_rectangle
    {g0 : MetricField} {kappa q0 r b G d : ℝ} {M : ℕ}
    (eta : metricPatchSet g0 kappa)
    {z : Coord → ℝ} (hclass : BoundedAdmissibleHeight (perturbedMetric g0 eta.val) M z)
    (hG : 0 ≤ G) (hd : 0 < d) (hkappa : 0 < kappa) (hr : 0 < r)
    (hab : -r ≤ b) (hb : b ≤ 0)
    (hLr : boundedClassWidth kappa M*r ≤ 1/20) (hq0 : |q0| ≤ 1/20)
    (hrsmall : heightQuotientJetBound G (M : ℝ) d (1/(M : ℝ))*
      (r+107*(boundedClassWidth kappa M*r)/100) ≤ 9/(100*boundedClassWidth kappa M))
    (hgB : ∀ i j k, k ≤ 4 → ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun a => perturbedMetric g0 eta.val a i j) p‖ ≤ G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(perturbedMetric g0 eta.val p).det|)
    (hcenter : |hessianQuotient (perturbedMetric g0 eta.val) z 0-q0| ≤
      1/(100*boundedClassWidth kappa M)) :
    ∃ radius lo hi : ℝ, boundedClassWidth kappa M*r < radius ∧ lo < -r ∧ b < hi ∧
      SmoothPositiveOn (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
        (coordinateRectangle radius lo hi) ∧
      ContDiffOn ℝ ∞ (heightInShearCoordinates z q0) (coordinateRectangle radius lo hi) ∧
      (∀ p ∈ coordinateRectangle radius lo hi,
        (covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
          (heightInShearCoordinates z q0) p).det =
            gaussianCurvature (metricInShearCoordinates (perturbedMetric g0 eta.val) q0) p*
              heightEnergy (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
                (heightInShearCoordinates z q0) p) ∧
      (∀ p ∈ coordinateRectangle radius lo hi,
        covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
          (heightInShearCoordinates z q0) p 0 0 ≠ 0) := by
  obtain ⟨U,_,hSU,hg,hz,hD,_,_,_⟩ := hclass.2.1
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (perturbedMetric g0 eta.val) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  let V := inverseShearCoordinates q0 ⁻¹' modelOpenSquare
  have hV : IsOpen V := modelOpenSquare_isOpen.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hgs := metricInShearCoordinates_smoothPositive hgO q0
  have hzs := heightInShearCoordinates_contDiffOn hzO q0
  have hgeom (p : Coord) (hp : p ∈ closedRectangle (-(boundedClassWidth kappa M*r))
      (boundedClassWidth kappa M*r) (-r) b) :=
    actual_patch_closed_strip_Hxx_floor eta hclass hG hd hkappa hr.le hb hLr hq0 hrsmall
      hgB hdet hcenter hp
  have hxx : ∀ p ∈ closedRectangle (-(boundedClassWidth kappa M*r))
      (boundedClassWidth kappa M*r) (-r) b,
      covHessian (metricInShearCoordinates (perturbedMetric g0 eta.val) q0)
        (heightInShearCoordinates z q0) p 0 0 ≠ 0 := by
    intro p hp
    exact abs_pos.mp ((boundedClassShearHxxFloor_pos hkappa hclass.1).trans_le (hgeom p hp).2)
  obtain ⟨radius,lo,hi,hradius,hlo,hhi,hrect,hxxrect⟩ :=
    exists_actual_Q_containing_rectangle hgs hzs hV
      (mul_pos (boundedClassWidth_pos kappa M) hr) hab (fun p hp => (hgeom p hp).1) hxx
  refine ⟨radius,lo,hi,hradius,hlo,hhi,
    ⟨fun i j => (hgs.1 i j).mono hrect,fun p hp => hgs.2 p (hrect hp)⟩,
    hzs.mono hrect,?_,hxxrect⟩
  intro p hp
  have hpO : inverseShearCoordinates q0 p ∈ modelOpenSquare := hrect hp
  exact darboux_in_shear_coordinates hgO hzO modelOpenSquare_isOpen q0 hpO
    (hD _ (modelOpenSquare_subset hpO))

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QClosedStripMargins
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.Perturbation.perturbationSeminorm_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise
namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem exists_uniform_Q_closed_strip_margins (G R M M0 : ℝ)
    {d nu c eta kappa : ℝ} (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hM0 : 0 ≤ M0)
    (hd : 0 < d) (hnu : 0 < nu) (hc : 0 < c) (heta : 0 < eta) (hkappa : 0 < kappa) :
    ∃ epsilon A : ℝ, 0 < epsilon ∧ 1 ≤ A ∧
      ∀ (g g0 : MetricField) (z z0 : Coord → ℝ) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn g0 U → IsOpen U →
      ContDiffOn ℝ ∞ z U → ContDiffOn ℝ ∞ z0 U →
      ∀ left right a b : ℝ, a ≤ b →
      closedRectangle left right a b ⊆ U →
      (∀ p ∈ closedRectangle left right a b, ‖p‖ ≤ R) →
      (∀ i j k, k ≤ 2 → ∀ p ∈ closedRectangle left right a b,
        ‖iteratedFDeriv ℝ k (fun x => g x i j) p‖ ≤ G) →
      (∀ i j k, k ≤ 2 → ∀ p ∈ closedRectangle left right a b,
        ‖iteratedFDeriv ℝ k (fun x => g0 x i j) p‖ ≤ G) →
      CoordinateBound z (closedRectangle left right a b) 3 M →
      CoordinateBound z0 (closedRectangle left right a b) 3 M0 →
      (∀ p ∈ closedRectangle left right a b, d ≤ |(g p).det|) →
      (∀ p ∈ closedRectangle left right a b, d ≤ |(g0 p).det|) →
      (∀ i j k, k ≤ 2 → ∀ p ∈ closedRectangle left right a b,
        ‖iteratedFDeriv ℝ k (fun x => g0 x i j - g x i j) p‖ ≤ epsilon) →
      (M + M0) * (b - a) ≤ epsilon →
      (∀ x ∈ Icc left right, qSolutionJet z0 (boxPoint x a) = qSolutionJet z (boxPoint x a)) →
      (∀ p ∈ closedRectangle left right a b, nu ≤ |covHessian g z p 0 0|) →
      (∀ p ∈ closedRectangle left right a b, c ≤ |covHessian g z p 1 1|) →
      (∀ p ∈ closedRectangle left right a b, eta ≤ heightEnergy g z p) →
      (∀ p ∈ closedRectangle left right a b, gaussianCurvature g p ≤ -kappa) →
      (∀ p ∈ closedRectangle left right a b,
        (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) →
      (∀ p ∈ closedRectangle left right a b,
        (hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p < 0) →
      ∀ x ∈ Icc left right, ∀ t ∈ Icc a b,
      (∀ sigma ∈ Icc (0 : ℝ) 1,
        nu / 2 ≤ |stateQDenominator g0 (qHeightJetSegment z0 z sigma (boxPoint x t))| ∧
        |stateQDenominator g0 (qHeightJetSegment z0 z sigma (boxPoint x t))| ≤ A ∧
        eta / 2 ≤ stateEnergy g0 (qHeightJetSegment z0 z sigma (boxPoint x t)) ∧
        ((nu * c) / 2) / A^2 ≤ qFirstCoefficient g0 5 (qHeightJetSegment z0 z sigma (boxPoint x t)) ∧
        ((kappa / 2) * (eta / 2)) / A^2 ≤
          (qFirstCoefficient g0 4 (qHeightJetSegment z0 z sigma (boxPoint x t)) / 2)^2 +
            qFirstCoefficient g0 5 (qHeightJetSegment z0 z sigma (boxPoint x t))) ∧
      ((nu * c) / 2) / A^2 ≤
        averagedQCoefficient g0 (qSolutionJet z0 (boxPoint x t)) (qSolutionJet z (boxPoint x t)) 5 ∧
      ((nu * c) / 2) / A^2 ≤
        (averagedQCoefficient g0 (qSolutionJet z0 (boxPoint x t)) (qSolutionJet z (boxPoint x t)) 4 / 2)^2 +
          averagedQCoefficient g0 (qSolutionJet z0 (boxPoint x t)) (qSolutionJet z (boxPoint x t)) 5 := by
  let W := max R (max M M0)
  obtain ⟨epsilon, A, hepsilon, hA, htransfer⟩ :=
    exists_uniform_Q_metric_state_margins G W hG hd hnu heta (mul_pos hnu hc) hkappa
  refine ⟨epsilon, A, hepsilon, hA, ?_⟩
  intro g g0 z z0 U hg hg0 hU hz hz0 left right a b hab hbox hpoint
    hgB hg0B hzB hz0B hdet hdet0 hmetric hwidth hinitial
    hxx hyy henergy hK hD htime x hx t ht
  have hpbox : boxPoint x t ∈ closedRectangle left right a b :=
    boxPoint_mem hx ht
  have hp : boxPoint x t ∈ U := hbox hpbox
  have hwB : ‖qSolutionJet z (boxPoint x t)‖ ≤ W := by
    apply qSolutionJet_norm_bound_of_words hR (hpoint _ hpbox)
    intro ds hds
    exact (hzB ds (hds.trans (by norm_num)) _ hpbox).trans (le_max_left _ _)
  have hw0B : ‖qSolutionJet z0 (boxPoint x t)‖ ≤ W := by
    apply qSolutionJet_norm_bound_of_words hR (hpoint _ hpbox)
    intro ds hds
    exact (hz0B ds (hds.trans (by norm_num)) _ hpbox).trans (le_max_right _ _)
  have hjet : ‖qSolutionJet z0 (boxPoint x t) - qSolutionJet z (boxPoint x t)‖ ≤ epsilon :=
    (qSolutionJet_distance_on_closed_strip hz hz0 hU hbox hx hab ht hM hM0
      hzB hz0B (hinitial x hx)).trans hwidth
  have hnum := stateNumerator_negative_of_solution_floors hg hU hz hp
    (hD _ hpbox) hnu hc (hxx _ hpbox) (hyy _ hpbox) (htime _ hpbox)
  have hstateE : eta ≤ stateEnergy g (qSolutionJet z (boxPoint x t)) := by
    unfold stateEnergy
    rw [statePoint_qSolutionJet, stateGradient_qSolutionJet, jetEnergy_at_height hg hp z]
    exact henergy _ hpbox
  have hsegment (sigma : ℝ) (hs : sigma ∈ Icc (0 : ℝ) 1) :=
    htransfer g g0 U hg hg0 hU (qSolutionJet z (boxPoint x t))
      (qHeightJetSegment z0 z sigma (boxPoint x t))
      (by rw [statePoint_qSolutionJet, statePoint_qHeightJetSegment])
      (by simpa only [statePoint_qSolutionJet] using hp)
      (fun i j k hk => by simpa only [statePoint_qSolutionJet] using hgB i j k hk _ hpbox)
      (fun i j k hk => by simpa only [statePoint_qSolutionJet] using hg0B i j k hk _ hpbox)
      hwB (stateSegment_norm_le hw0B hwB hs)
      (by simpa only [statePoint_qSolutionJet] using hdet _ hpbox)
      (by simpa only [statePoint_qSolutionJet] using hdet0 _ hpbox)
      (fun i j k hk => by simpa only [statePoint_qSolutionJet] using hmetric i j k hk _ hpbox)
      ((stateSegment_sub_right_norm_le hs).trans hjet)
      (by simpa only [stateQDenominator_qSolutionJet] using hxx _ hpbox) hstateE hnum
      (by simpa only [statePoint_qSolutionJet] using hK _ hpbox)
  refine ⟨hsegment, ?_⟩
  apply averagedQPrincipal_margin hg0 hU
  · intro sigma hs
    refine ⟨?_, ?_⟩
    · change statePoint (qHeightJetSegment z0 z sigma (boxPoint x t)) ∈ U
      rw [statePoint_qHeightJetSegment]
      exact hp
    · have hm := (hsegment sigma hs).1
      exact abs_pos.mp ((half_pos hnu).trans_le hm)
  · intro sigma hs
    exact (hsegment sigma hs).2.2.2.1

end SmoothLocal.HighEquation

end

end OAI
end


