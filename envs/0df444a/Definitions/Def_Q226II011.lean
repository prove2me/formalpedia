-- Prove2me | Definitions.Def_Q226II011
-- name    : Q226II011
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:47:31.591311+00:00
-- url     : https://prove2.me/theorems/676a0ca0-ec96-4a51-b756-ff9726426d5f
-- title:
--   Definitions bundle Q226II011 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 62 declarations of OpenAI's Lean: 1 definition and 61 theorems. The definitions and types are `OAI.SmoothLocal.Pulse.qMetricFirstError`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Calculus_ClosedSquareJetBounds`, `IsometricImmersion_Calculus_HessianJetBounds`, `IsometricImmersion_Calculus_HessianQuotientLowBounds`, `IsometricImmersion_Calculus_SecondJetExtraction`, `IsometricImmersion_Caps_HeightCapLowData`, `IsometricImmersion_Caps_UniformOriginalDataCapEstimate`, `IsometricImmersion_Coordinates_CoordinateFirstBounds`, `IsometricImmersion_Curvature_CurvatureFirstBounds`, `IsometricImmersion_Darboux_ActualHighDrift`, `IsometricImmersion_Darboux_DarbouxEquation`, `IsometricImmersion_Darboux_HeightPrincipalBounds`, `IsometricImmersion_Darboux_MixedDarbouxElimination`, `IsometricImmersion_Darboux_QMetricDensityDecomposition`, `IsometricImmersion_Darboux_SixVariableDarboux`, `IsometricImmersion_Darboux_SixVariableLinearization`, `IsometricImmersion_Energy_ActualRemainderL2`, `IsometricImmersion_Energy_DirectedFarNegative`, `IsometricImmersion_Energy_HeightEnergyJetBounds`, `IsometricImmersion_Energy_MixedRemainderL2`, `IsometricImmersion_Energy_PatchDirectedCoercivity`, `IsometricImmersion_Estimates_ActualHighEquation`, `IsometricImmersion_Estimates_ActualRemainderFactors`, `IsometricImmersion_Estimates_ActualRemainderRegularity`, `IsometricImmersion_Estimates_LargestBlockLinearization`, `IsometricImmersion_Estimates_MixedRemainderFactors`, `IsometricImmersion_Flows_ActualFlowHighEquation`, `IsometricImmersion_Flows_FlowHeightCoefficients`, `IsometricImmersion_Flows_HeightFlowUniformBounds`, `IsometricImmersion_Flows_PatchFlowCoercivity`, `IsometricImmersion_Flows_UniformRichPatchFlow`, `IsometricImmersion_Immersions_HeightCoefficientClosedBounds`, `IsometricImmersion_Immersions_HeightPFirstBounds`, `IsometricImmersion_Taylor_ActualDarbouxFaa`, `IsometricImmersion_Taylor_TopChainExtraction`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II007`, `Q226II008` and `Q226II009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II014` and `Q226II015`.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 334; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
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
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II007
import Definitions.Def_Q226II008
import Definitions.Def_Q226II009

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_HessianQuotientLowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {M c : ℝ}

theorem hessianQuotient_coordinate_bound_through_three
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hM : 0 ≤ M) (hc : 0 < c)
    (hH : ∀ i j : Fin 2, ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U,
      |iteratedCoordPartial ds (fun x => covHessian g z x i j) p| ≤ M)
    (hden : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U ∧
      ∀ ds : List (Fin 2), ds.length ≤ 3 → ∀ p ∈ U,
        |iteratedCoordPartial ds (hessianQuotient g z) p| ≤ LowQuotient.boundThroughThree M c := by
  have hxy := covHessian_contDiffOn hg hU hz 0 1
  have hyy := covHessian_contDiffOn hg hU hz 1 1
  refine ⟨hessianQuotient_contDiffOn hg hU hz (LowQuotient.denominator_ne_zero hc hden), ?_⟩
  intro ds hlen p hp
  exact LowQuotient.quotient_bound_through_three hxy hyy hU hM hc (hH 0 1) (hH 1 1) hden ds hlen hp

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_HessianJetBounds
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

theorem hessianQuotient_bound_from_metric_height_jets
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    ContDiffOn ℝ ∞ (hessianQuotient g z) U ∧
      CoordinateBound (hessianQuotient g z) U 3
        (LowQuotient.boundThroughThree (hessianJetBound G Z d) c) := by
  exact hessianQuotient_coordinate_bound_through_three hg hU hz
    (hessianJetBound_nonneg hG hZ hd) hc
    (fun i j => covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet i j) hyy

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_DarbouxEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem solvedDarboux_at_height
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (hD : (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    coordPartial 0 (coordPartial 0 z) p =
      solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p)
        (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p) := by
  have hdet : covHessian g z p 0 0 * covHessian g z p 1 1 -
      (covHessian g z p 0 1) ^ 2 = gaussianCurvature g p * heightEnergy g z p := by
    simpa only [Matrix.det_fin_two, covHessian_symm hg hU hz hp 1 0, pow_two] using hD
  have hsolve : covHessian g z p 0 0 =
      ((covHessian g z p 0 1) ^ 2 + gaussianCurvature g p * heightEnergy g z p) /
        covHessian g z p 1 1 := by
    apply (eq_div_iff hyy).2
    linarith [hdet]
  change coordPartial 0 (coordPartial 0 z) p -
    jetConnection g p 0 0 (fun i => coordPartial i z p) = _ at hsolve
  rw [solvedDarboux, jetNumerator, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z]
  linarith [hsolve]

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

theorem exists_open_quotient_domain_with_closed_low_bounds
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      ContDiffOn ℝ ∞ (hessianQuotient g z) V ∧
      CoordinateBound (hessianQuotient g z) modelSquare 3
        (LowQuotient.boundThroughThree (hessianJetBound G Z d) c) := by
  obtain ⟨V, hV, hSV, hVU, hVne, hqV⟩ := exists_open_hessianQuotient_domain hg hU hz hSU
    (LowQuotient.denominator_ne_zero hc hyy)
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun a b => (hg.1 a b).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hBI := (hessianQuotient_bound_from_metric_height_jets hgI isOpen_interior (hz.mono hIU)
    hG hZ hd hc (fun a b => (hgB a b).restrict_domain interior_subset)
    (hzB.restrict_domain interior_subset) (fun p hp => hdet p (interior_subset hp))
    (fun p hp => hyy p (interior_subset hp))).2
  exact ⟨V, hV, hSV, hVU, hVne, hqV,
    CoordinateBound.of_modelSquare_interior hqV hV hSV hBI⟩

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SixVariableDarboux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord}

theorem stateNumerator_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (stateNumerator g) (stateBaseDomain U) :=
  ((stateMixed_contDiffOn hg hU).pow 2).add
    (((gaussianCurvature_contDiffOn hg hU).comp statePoint_contDiff.contDiffOn
      (fun _ hw => hw)).mul (stateEnergy_contDiffOn hg))

theorem sixVariableP_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U) :
    ContDiffOn ℝ ∞ (sixVariableP g) (darbouxStateDomain g U) := by
  have hsub : darbouxStateDomain g U ⊆ stateBaseDomain U := fun w hw => hw.1
  exact ((stateConnection_contDiffOn hg hU 0 0).mono hsub).add
    (((stateNumerator_contDiffOn hg hU).mono hsub).div
      ((stateDenominator_contDiffOn hg hU).mono hsub) (fun w hw => hw.2))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ActualDarbouxFaa
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem sixVariableP_contDiffAt_solutionJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    ContDiffAt ℝ ∞ (sixVariableP g) (solutionJet z p) :=
  (sixVariableP_contDiffOn hg hU).contDiffAt
    ((darbouxStateDomain_isOpen hg hU).mem_nhds (solutionJet_mem_domain g z hp hyy))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SixVariableLinearization
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem sixVariableP_gradient_axis
    {g : MetricField} {U : Set Coord} {w : DarbouxState}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hw : w ∈ darbouxStateDomain g U) (i : Fin 2) :
    fderiv ℝ (sixVariableP g) w (Pi.single (gradientStateIndex i) 1) =
      coordPartial i (solvedDarboux g (statePoint w) (w 4) (w 5)) (stateGradient w) := by
  have hP : DifferentiableAt ℝ (sixVariableP g) w :=
    ((sixVariableP_contDiffOn hg hU).contDiffAt
      ((darbouxStateDomain_isOpen hg hU).mem_nhds hw)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update w (gradientStateIndex i) t)) =
      (fun t => solvedDarboux g (statePoint w) (w 4) (w 5) (Function.update (stateGradient w) i t)) :=
    funext (sixVariableP_update_gradient g w i)
  rw [heq]
  have hi : w (gradientStateIndex i) = stateGradient w i := by
    fin_cases i <;> simp [gradientStateIndex, stateGradient]
  rw [hi]
  exact (fderiv_axis_eq_deriv_update
    (solvedDarboux_first_variables_differentiableAt g (statePoint w) (stateGradient w) (w 4) (w 5) hw.2) i).symm

theorem sixVariableP_gradient_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single (gradientStateIndex i) 1) =
      heightPFirst g z i p := by
  rw [sixVariableP_gradient_axis hg hU (solutionJet_mem_domain g z hp hyy) i,
    statePoint_solutionJet, stateGradient_solutionJet]
  rfl

theorem sixVariableP_mixed_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 4 1) = 2 * hessianQuotient g z p := by
  have hP := (sixVariableP_contDiffAt_solutionJet hg hU hp hyy).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update (solutionJet z p) 4 t)) =
      (fun t => solvedDarboux g p t (coordPartial 1 (coordPartial 1 z) p) (fun i => coordPartial i z p)) := by
    funext t
    rw [sixVariableP_update_mixed, statePoint_solutionJet, stateGradient_solutionJet]
    rfl
  rw [heq]
  change deriv (fun t => solvedDarboux g p t (coordPartial 1 (coordPartial 1 z) p)
    (fun i => coordPartial i z p)) (coordPartial 0 (coordPartial 1 z) p) = _
  rw [solvedDarboux_deriv_b g p _ _ _ hyy, jetMixed_at_height, jetYY_at_height]
  rfl

theorem sixVariableP_yy_axis_at_height
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 5 1) =
      -((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) := by
  have hP := (sixVariableP_contDiffAt_solutionJet hg hU hp hyy).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [fderiv_axis_eq_deriv_update hP]
  have heq : (fun t => sixVariableP g (Function.update (solutionJet z p) 5 t)) =
      (fun t => solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p) t (fun i => coordPartial i z p)) := by
    funext t
    rw [sixVariableP_update_yy, statePoint_solutionJet, stateGradient_solutionJet]
    rfl
  rw [heq]
  change deriv (fun t => solvedDarboux g p (coordPartial 0 (coordPartial 1 z) p) t
    (fun i => coordPartial i z p)) (coordPartial 1 (coordPartial 1 z) p) = _
  rw [solvedDarboux_deriv_c g p _ _ _ hyy, jetMixed_at_height, jetYY_at_height,
    jetEnergy_at_height hg hp z]
  unfold hessianQuotient darbouxG
  ring

theorem sixVariableP_vertical_direction
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (v : DarbouxState) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    fderiv ℝ (sixVariableP g) (solutionJet z p) v =
      heightPFirst g z 0 p * v 2 + heightPFirst g z 1 p * v 3 +
        2 * hessianQuotient g z p * v 4 -
        ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) * v 5 := by
  have he : v = v 2 • (Pi.single 2 (1 : ℝ) : DarbouxState) +
      v 3 • Pi.single 3 1 + v 4 • Pi.single 4 1 + v 5 • Pi.single 5 1 := by
    ext i
    fin_cases i <;> simp [hv0, hv1]
  have h0 : fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 2 1) = heightPFirst g z 0 p := by
    simpa only [gradientStateIndex, ↓reduceIte] using sixVariableP_gradient_axis_at_height hg hU hp hyy 0
  have h1 : fderiv ℝ (sixVariableP g) (solutionJet z p) (Pi.single 3 1) = heightPFirst g z 1 p := by
    simpa only [gradientStateIndex, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte] using
      sixVariableP_gradient_axis_at_height hg hU hp hyy 1
  have hl := congrArg (fderiv ℝ (sixVariableP g) (solutionJet z p)) he
  simp only [map_add, map_smul, h0, h1, sixVariableP_mixed_axis_at_height hg hU hp hyy,
    sixVariableP_yy_axis_at_height hg hU hp hyy, smul_eq_mul] at hl
  rw [hl]
  ring

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_LargestBlockLinearization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem fullBlockPartition_actual_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : (![x, y] : Coord) ∈ U) (hyy : covHessian g z ![x, y] 1 1 ≠ 0)
    (ell : ℕ) (hell : 2 ≤ ell) :
    darbouxFaaTerm g z x y (fullBlockPartition ell (by omega)) =
      directLinearization g z (verticalJet z ell) ![x, y] := by
  rw [fullBlockPartition_term, solutionJetCurve_iteratedDeriv hU hz hp ell hell]
  change fderiv ℝ (sixVariableP g) (solutionJet z ![x, y]) _ = _
  rw [sixVariableP_vertical_direction hg hU hp hyy _ (by rfl) (by rfl)]
  rfl

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowHeightCoefficients
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

variable {g : MetricField} {z u : Coord → ℝ} {U : Set Coord} {p : Coord} {Y : ℝ → ℝ → ℝ}

theorem heightChartA_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) :
    ContDiffOn ℝ ∞ (heightChartA g z Y) capChartDomain :=
  (capPullback_contDiffOn hY (heightOriginalA_contDiffOn hg hU hz hyy) hmap).mul
    ((capChartRho_contDiffOn hY hvar).pow 2)

theorem heightChartC_contDiffOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hE : ∀ p ∈ U, 0 < heightEnergy g z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightChartC g z Y ell) capChartDomain := by
  have hA := heightChartA_contDiffOn hg hU hz hyy hY hvar hmap
  have hr := heightChartRemainder_contDiffOn hg hU hz hyy hE hY hvar hmap ell
  exact ((contDiffOn_const.mul (partial_contDiffOn hA capChartDomain_isOpen 1)).add (hA.mul hr)).congr
    (fun _ hp => heightChartC_factor hg hU hz hD hyy hE hY hvar hmap hp ell)

theorem height_coefficient_operator_transport
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-(hessianQuotient g z) (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (hu : ContDiffOn ℝ ∞ u U)
    (hp : p ∈ capChartDomain) (ell : ℕ) :
    capPullback Y (driftOperator (hessianQuotient g z) (heightOriginalA g z)
      (heightOriginalB g z ell) (heightOriginalC0 g z ell) u) p =
      multiplierOperator (heightChartA g z Y) (heightChartB g z Y ell)
        (heightChartC g z Y ell) (capPullback Y u) p :=
  cap_driftOperator_transport _ _ _ hY hode hvar (hessianQuotient_contDiffOn hg hU hz hyy)
    hu hU hmap hp

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TopChainExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actualP_top_chain_expansion
    {g : SmoothLocal.Geometry.MetricField} {z : SmoothLocal.Geometry.Coord → ℝ}
    {U : Set SmoothLocal.Geometry.Coord} {x y : ℝ}
    (hg : SmoothLocal.Geometry.SmoothPositiveOn g U) (hU : IsOpen U)
    (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, SmoothLocal.Geometry.covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : SmoothLocal.Geometry.Coord) ∈ U) (m : ℕ) :
    iteratedDeriv (m + 3) (sixVariableP g ∘ solutionJetCurve z x) y =
      chainTerm (sixVariableP g) (solutionJetCurve z x) (ChainWord.single (m + 3)) y +
      (m + 3 : ℝ) * chainTerm (sixVariableP g) (solutionJetCurve z x)
        (ChainWord.pair 1 (m + 2)) y +
      chainSum (sixVariableP g) (solutionJetCurve z x) (topResidualWords m) y := by
  let I : Set ℝ := {t | (![x, t] : SmoothLocal.Geometry.Coord) ∈ U}
  have hI : IsOpen I := hU.preimage (verticalPoint_contDiff x).continuous
  have hJ : ContDiffOn ℝ ∞ (solutionJetCurve z x) I := by
    intro t ht
    exact (solutionJetCurve_contDiffAt hU hz ht).contDiffWithinAt
  have hmap : MapsTo (solutionJetCurve z x) I (darbouxStateDomain g U) := by
    intro t ht
    exact solutionJet_mem_domain g z ht (hyy _ ht)
  exact top_chain_expansion (darbouxStateDomain_isOpen hg hU) hI
    (sixVariableP_contDiffOn hg hU) hJ hmap m y hp

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_SecondJetExtraction
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem sixVariableP_second_vertical_direction
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ r ∈ U, covHessian g z r 1 1 ≠ 0) (hp : p ∈ U)
    (v : DarbouxState) (hv0 : v 0 = 0) (hv1 : v 1 = 0) :
    iteratedFDeriv ℝ 2 (sixVariableP g) (solutionJet z p)
        ![coordPartial 1 (solutionJet z) p, v] =
      coordPartial 1 (heightPFirst g z 0) p * v 2 +
      coordPartial 1 (heightPFirst g z 1) p * v 3 +
      2 * coordPartial 1 (hessianQuotient g z) p * v 4 -
      coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
        gaussianCurvature g r * darbouxG g z r) p * v 5 := by
  rw [second_fderiv_comp_constant_direction
    (sixVariableP_contDiffAt_solutionJet hg hU hp (hyy _ hp))
    (((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  have heq : (fun r => fderiv ℝ (sixVariableP g) (solutionJet z r) v) =ᶠ[𝓝 p]
      (fun r => heightPFirst g z 0 r * v 2 + heightPFirst g z 1 r * v 3 +
        2 * hessianQuotient g z r * v 4 -
        ((hessianQuotient g z r)^2 + gaussianCurvature g r * darbouxG g z r) * v 5) := by
    filter_upwards [hU.mem_nhds hp] with r hr
    exact sixVariableP_vertical_direction hg hU hr (hyy _ hr) v hv0 hv1
  have h0 := ((heightPFirst_contDiffOn hg hU hz hyy 0).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h1 := ((heightPFirst_contDiffOn hg hU hz hyy 1).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hq := ((hessianQuotient_contDiffOn hg hU hz hyy).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hK := ((gaussianCurvature_contDiffOn hg hU).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hG := ((darbouxG_contDiffOn hg hU hz hyy).contDiffAt
    (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have ha : DifferentiableAt ℝ (fun r => (hessianQuotient g z r)^2 +
      gaussianCurvature g r * darbouxG g z r) p := (hq.pow 2).add (hK.mul hG)
  have hd := (((h0.hasFDerivAt.mul_const (v 2)).add
    (h1.hasFDerivAt.mul_const (v 3))).add
    ((hq.hasFDerivAt.const_mul 2).mul_const (v 4))).sub (ha.hasFDerivAt.mul_const (v 5))
  simp only [Pi.add_def, Pi.sub_def] at hd
  unfold coordPartial
  rw [heq.fderiv_eq]
  change fderiv ℝ (fun r => heightPFirst g z 0 r * v 2 + heightPFirst g z 1 r * v 3 +
      2 * hessianQuotient g z r * v 4 -
      ((hessianQuotient g z r)^2 + gaussianCurvature g r * darbouxG g z r) * v 5) p
      (Pi.single 1 1) = _
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

theorem actualP_pair_extract_secondJet
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : Coord) ∈ U) (n : ℕ) (hn : 2 ≤ n) :
    chainTerm (sixVariableP g) (solutionJetCurve z x) (ChainWord.pair 1 n) y =
      secondJetCorrection g z (verticalJet z (n + 1)) ![x, y] +
        firstJetPairRemainder g z n ![x, y] := by
  have hfirst : iteratedDeriv 1 (solutionJetCurve z x) y =
      coordPartial 1 (solutionJet z) ![x, y] :=
    verticalJet_slice hU (solutionJet_contDiffOn hU hz) x 1 y hp
  rw [chainTerm_pair_eq, hfirst, solutionJetCurve_iteratedDeriv hU hz hp n hn]
  change iteratedFDeriv ℝ 2 (sixVariableP g) (solutionJet z ![x, y]) _ = _
  rw [sixVariableP_second_vertical_direction hg hU hz hyy hp _ (by rfl) (by rfl)]
  change
    coordPartial 1 (heightPFirst g z 0) ![x, y] * coordPartial 0 (verticalJet z n) ![x, y] +
    coordPartial 1 (heightPFirst g z 1) ![x, y] * coordPartial 1 (verticalJet z n) ![x, y] +
    2 * coordPartial 1 (hessianQuotient g z) ![x, y] *
      coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y] -
    coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
      gaussianCurvature g r * darbouxG g z r) ![x, y] *
      coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y] = _
  unfold secondJetCorrection firstJetPairRemainder
  change _ =
    (2 * coordPartial 1 (hessianQuotient g z) ![x, y] *
        coordPartial 0 (coordPartial 1 (verticalJet z n)) ![x, y] -
      coordPartial 1 (fun r => (hessianQuotient g z r)^2 +
        gaussianCurvature g r * darbouxG g z r) ![x, y] *
        coordPartial 1 (coordPartial 1 (verticalJet z n)) ![x, y]) + _
  ring

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_CoordinateFirstBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.CoordinateBound

theorem congr_on {f h : Coord → ℝ} {U : Set Coord} {n : ℕ} {M : ℝ}
    (hU : IsOpen U) (hf : CoordinateBound f U n M) (he : EqOn h f U) :
    CoordinateBound h U n M := by
  intro ds hds p hp
  have hlocal : h =ᶠ[𝓝 p] f := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact he hx
  rw [(iteratedCoordPartial_eventuallyEq hlocal ds).self_of_nhds]
  exact hf ds hds p hp

theorem div_through_one {f h : Coord → ℝ} {U : Set Coord} {A B c : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U) (hU : IsOpen U)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c)
    (hfB : CoordinateBound f U 1 A) (hhB : CoordinateBound h U 1 B)
    (hden : ∀ p ∈ U, c ≤ |h p|) :
    CoordinateBound (fun x => f x / h x) U 1 (A / c + (A + B * (A / c)) / c) := by
  have hne := LowQuotient.denominator_ne_zero hc hden
  have hval (p : Coord) (hp : p ∈ U) : |f p / h p| ≤ A / c :=
    LowQuotient.abs_div_bound hA (hfB [] (by norm_num) p hp) hc (hden p hp)
  have h0 : 0 ≤ A / c := by positivity
  have h1 : 0 ≤ (A + B * (A / c)) / c := by positivity
  intro ds hds p hp
  cases ds with
  | nil => exact (hval p hp).trans (by linarith)
  | cons i ds =>
    cases ds with
    | nil =>
      rw [LowQuotient.quotient_one hf hh hU hp hne i]
      have hprod : |coordPartial i h p * (f p / h p)| ≤ B * (A / c) := by
        rw [abs_mul]
        exact mul_le_mul (hhB [i] (by norm_num) p hp) (hval p hp) (abs_nonneg _) hB
      have hnum := (abs_sub (coordPartial i f p) (coordPartial i h p * (f p / h p))).trans
        (add_le_add (hfB [i] (by norm_num) p hp) hprod)
      exact (LowQuotient.abs_div_bound (by positivity) hnum hc (hden p hp)).trans (by linarith)
    | cons j ds => simp only [List.length_cons] at hds; omega

end SmoothLocal.Geometry.CoordinateBound

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureFirstBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord} {G d : ℝ}

theorem riemann_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) (l k i j : Fin 2) :
    CoordinateBound (riemann g l k i j) U 1 (riemannFirstBound G d) := by
  have hΓ := christoffelJetBound_nonneg hG hd
  have hΓB (a b c : Fin 2) := christoffel_coordinate_bound hg hU hG hd hgB hdet a b c
  have hΓ1 (a b c : Fin 2) : CoordinateBound (christoffel g a b c) U 1 (christoffelJetBound G d) :=
    (hΓB a b c).mono (by norm_num) le_rfl
  have hΓd (a b c e : Fin 2) : CoordinateBound (coordPartial e (christoffel g a b c)) U 1
      (christoffelJetBound G d) :=
    ((hΓB a b c).mono (by norm_num : 2 ≤ 3) le_rfl).partial_bound e
  have hΓs (a b c : Fin 2) := christoffel_contDiffOn hg hU a b c
  have hm (m : Fin 2) := CoordinateBound.sub
    ((hΓs m j k).mul (hΓs l i m)) ((hΓs m i k).mul (hΓs l j m)) hU
    (CoordinateBound.mul_through_one (hΓs m j k) (hΓs l i m) hU hΓ hΓ (hΓ1 m j k) (hΓ1 l i m))
    (CoordinateBound.mul_through_one (hΓs m i k) (hΓs l j m) hU hΓ hΓ (hΓ1 m i k) (hΓ1 l j m))
  have hms (m : Fin 2) := ((hΓs m j k).mul (hΓs l i m)).sub ((hΓs m i k).mul (hΓs l j m))
  have hs := CoordinateBound.add (hms 0) (hms 1) hU (hm 0) (hm 1)
  have hdiff := CoordinateBound.sub (partial_contDiffOn (hΓs l j k) hU i)
    (partial_contDiffOn (hΓs l i k) hU j) hU (hΓd l j k i) (hΓd l i k j)
  have hb := CoordinateBound.add
    ((partial_contDiffOn (hΓs l j k) hU i).sub (partial_contDiffOn (hΓs l i k) hU j))
    ((hms 0).add (hms 1)) hU hdiff hs
  convert hb using 1 <;> first
    | (funext p; simp only [riemann, Fin.sum_univ_two])
    | (dsimp [riemannFirstBound]; ring)

theorem gaussianCurvature_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|) :
    CoordinateBound (gaussianCurvature g) U 1 (curvatureFirstBound G d) := by
  have hR := riemannFirstBound_nonneg hG hd
  have hprod (l : Fin 2) := CoordinateBound.mul_through_one (hg.1 0 l)
    (riemann_contDiffOn hg hU l 1 0 1) hU hG hR
    ((hgB 0 l).mono (by norm_num) le_rfl)
    (riemann_coordinate_bound_one hg hU hG hd hgB hdet l 1 0 1)
  have hprodS (l : Fin 2) := (hg.1 0 l).mul (riemann_contDiffOn hg hU l 1 0 1)
  have hsum := CoordinateBound.add (hprodS 0) (hprodS 1) hU (hprod 0) (hprod 1)
  have hn : CoordinateBound (fun p => g p 0 0 * riemann g 0 1 0 1 p +
      g p 0 1 * riemann g 1 1 0 1 p) U 1 (curvatureNumeratorFirstBound G d) := by
    convert hsum using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [curvatureNumeratorFirstBound]
    ring
  have hnb : 0 ≤ curvatureNumeratorFirstBound G d := by dsimp [curvatureNumeratorFirstBound] <;> positivity
  have hdb : CoordinateBound (fun p => (g p).det) U 1 (16 * G^2) :=
    (metricDet_coordinate_bound hg hU hG (fun i j => (hgB i j).mono (by norm_num) le_rfl)).mono
      (by norm_num) le_rfl
  have hb := CoordinateBound.div_through_one ((hprodS 0).add (hprodS 1))
    (metricDet_contDiffOn hg) hU hnb (by positivity : 0 ≤ 16 * G^2) hd hn hdb hdet
  convert hb using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  funext p
  simp only [gaussianCurvature, Fin.sum_univ_two]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_HeightEnergyJetBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

theorem heightEnergy_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hzB : CoordinateBound z U 4 Z) :
    CoordinateBound (heightEnergy g z) U 3 (heightEnergyJetBound G Z) := by
  have hzi (i : Fin 2) := partial_contDiffOn hz hU i
  have hzBi (i : Fin 2) : CoordinateBound (coordPartial i z) U 3 Z := hzB.partial_bound i
  have hsquare (i : Fin 2) : CoordinateBound (fun p => (coordPartial i z p)^2) U 3 (8 * Z^2) := by
    convert CoordinateBound.mul_through_three (hzi i) (hzi i) hU hZ hZ (hzBi i) (hzBi i) using 1 <;>
      simp only [pow_two, mul_assoc]
  have hdiag0 := CoordinateBound.mul_through_three (hg.1 1 1) ((hzi 0).pow 2) hU hG
    (by positivity : 0 ≤ 8 * Z^2) (hgB 1 1) (hsquare 0)
  have hdiag1 := CoordinateBound.mul_through_three (hg.1 0 0) ((hzi 1).pow 2) hU hG
    (by positivity : 0 ≤ 8 * Z^2) (hgB 0 0) (hsquare 1)
  have hsum := CoordinateBound.add (hg.1 0 1) (hg.1 1 0) hU (hgB 0 1) (hgB 1 0)
  have hcross1 := CoordinateBound.mul_through_three ((hg.1 0 1).add (hg.1 1 0))
    (hzi 0) hU (by positivity : 0 ≤ G + G) hZ hsum (hzBi 0)
  have hcross := CoordinateBound.mul_through_three
    (((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)) (hzi 1) hU
    (by positivity : 0 ≤ 8 * (G + G) * Z) hZ hcross1 (hzBi 1)
  have hinner := CoordinateBound.add
    (((hg.1 1 1).mul ((hzi 0).pow 2)).sub ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1)))
    ((hg.1 0 0).mul ((hzi 1).pow 2)) hU
    (CoordinateBound.sub ((hg.1 1 1).mul ((hzi 0).pow 2))
      ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1)) hU hdiag0 hcross) hdiag1
  have hfull := CoordinateBound.sub (metricDet_contDiffOn hg)
    ((((hg.1 1 1).mul ((hzi 0).pow 2)).sub
      ((((hg.1 0 1).add (hg.1 1 0)).mul (hzi 0)).mul (hzi 1))).add
        ((hg.1 0 0).mul ((hzi 1).pow 2))) hU (metricDet_coordinate_bound hg hU hG hgB) hinner
  have hc : 16 * G^2 + (8 * G * (8 * Z^2) + 8 * (8 * (G + G) * Z) * Z + 8 * G * (8 * Z^2)) =
      heightEnergyJetBound G Z := by dsimp [heightEnergyJetBound] <;> ring
  rw [hc] at hfull
  exact CoordinateBound.congr_on hU hfull (fun p hp => heightEnergy_polynomial z hg hp)

theorem darbouxG_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) :
    CoordinateBound (darbouxG g z) U 3 (darbouxGJetBound G Z d c) := by
  have hH := hessianJetBound_nonneg hG hZ hd
  have hE := heightEnergyJetBound_nonneg (Z := Z) hG
  have hh := covHessian_contDiffOn hg hU hz 1 1
  have hhB := covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet 1 1
  have hhsq : CoordinateBound (fun p => (covHessian g z p 1 1)^2) U 3
      (8 * (hessianJetBound G Z d)^2) := by
    convert CoordinateBound.mul_through_three hh hh hU hH hH hhB hhB using 1 <;>
      simp only [pow_two, mul_assoc]
  have hEB := heightEnergy_coordinate_bound hg hU hz hG hZ
    (fun i j => (hgB i j).mono (by norm_num) le_rfl) (hzB.mono (by norm_num) le_rfl)
  let N := heightEnergyJetBound G Z + 8 * (hessianJetBound G Z d)^2
  have hN : 0 ≤ N := by dsimp [N] <;> positivity
  have hn : heightEnergyJetBound G Z ≤ N := by dsimp [N] <;> nlinarith [sq_nonneg (hessianJetBound G Z d)]
  have hb : 8 * (hessianJetBound G Z d)^2 ≤ N := by dsimp [N] <;> linarith
  have hden (p : Coord) (hp : p ∈ U) : c^2 ≤ |(covHessian g z p 1 1)^2| := by
    rw [abs_pow]
    exact pow_le_pow_left₀ hc.le (hyy p hp) 2
  intro ds hds p hp
  exact LowQuotient.quotient_bound_through_three (heightEnergy_contDiffOn hg hU hz)
    (hh.pow 2) hU hN (pow_pos hc 2) (hEB.mono le_rfl hn) (hhsq.mono le_rfl hb) hden ds hds hp

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_HeightPFirstBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

theorem height_jetEnergy_first_coordinate_bound
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 3 G)
    (hzB : CoordinateBound z U 4 Z) (i : Fin 2) :
    CoordinateBound (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p)) U 3
      (32 * G * Z) := by
  have hzS (j : Fin 2) := partial_contDiffOn hz hU j
  have hzD (j : Fin 2) : CoordinateBound (coordPartial j z) U 3 Z := hzB.partial_bound j
  have hdiag (a j : Fin 2) := CoordinateBound.const_mul
    ((hg.1 a a).mul (hzS j)) hU
    (CoordinateBound.mul_through_three (hg.1 a a) (hzS j) hU hG hZ (hgB a a) (hzD j)) (2 : ℝ)
  have hoff (j : Fin 2) := CoordinateBound.mul_through_three
    ((hg.1 0 1).add (hg.1 1 0)) (hzS j) hU (by positivity : 0 ≤ G + G) hZ
    (CoordinateBound.add (hg.1 0 1) (hg.1 1 0) hU (hgB 0 1) (hgB 1 0)) (hzD j)
  fin_cases i
  · have hb := CoordinateBound.sub (((hg.1 0 1).add (hg.1 1 0)).mul (hzS 1))
      (contDiffOn_const.mul ((hg.1 1 1).mul (hzS 0))) hU (hoff 1) (hdiag 1 0)
    have hc : 8 * (G + G) * Z + |(2 : ℝ)| * (8 * G * Z) = 32 * G * Z := by norm_num; ring
    rw [hc] at hb
    apply CoordinateBound.congr_on hU hb
    intro p hp
    change coordPartial 0 (jetEnergy g p) (fun r => coordPartial r z p) =
      (g p 0 1 + g p 1 0) * coordPartial 1 z p - 2 * (g p 1 1 * coordPartial 0 z p)
    rw [coordPartial_jetEnergy]
    norm_num
    ring
  · have hb := CoordinateBound.sub (((hg.1 0 1).add (hg.1 1 0)).mul (hzS 0))
      (contDiffOn_const.mul ((hg.1 0 0).mul (hzS 1))) hU (hoff 0) (hdiag 0 1)
    have hc : 8 * (G + G) * Z + |(2 : ℝ)| * (8 * G * Z) = 32 * G * Z := by norm_num; ring
    rw [hc] at hb
    apply CoordinateBound.congr_on hU hb
    intro p hp
    change coordPartial 1 (jetEnergy g p) (fun r => coordPartial r z p) =
      (g p 0 1 + g p 1 0) * coordPartial 0 z p - 2 * (g p 0 0 * coordPartial 1 z p)
    rw [coordPartial_jetEnergy]
    norm_num
    ring

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}

theorem height_christoffelAlongD_coordinate_bound
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) (i : Fin 2) :
    CoordinateBound (fun p => christoffelAlongD g p (hessianQuotient g z p) i) U 3
      (heightAlongDJetBound G Z d c) := by
  obtain ⟨hqs, hqb⟩ := hessianQuotient_bound_from_metric_height_jets hg hU hz hG hZ hd hc hgB hzB hdet hyy
  have hqN := heightQuotientJetBound_nonneg hG hZ hd hc
  have hΓN := christoffelJetBound_nonneg hG hd
  have hΓs (a b : Fin 2) := christoffel_contDiffOn hg hU i a b
  have hΓb (a b : Fin 2) := christoffel_coordinate_bound hg hU hG hd hgB hdet i a b
  have hqb' : CoordinateBound (hessianQuotient g z) U 3 (heightQuotientJetBound G Z d c) := hqb
  have hqΓ := CoordinateBound.mul_through_three hqs (hΓs 0 1) hU hqN hΓN hqb' (hΓb 0 1)
  have htwice := CoordinateBound.const_mul (hqs.mul (hΓs 0 1)) hU hqΓ (2 : ℝ)
  have hqsq : CoordinateBound (fun p => (hessianQuotient g z p)^2) U 3
      (8 * (heightQuotientJetBound G Z d c)^2) := by
    convert CoordinateBound.mul_through_three hqs hqs hU hqN hqN hqb' hqb' using 1 <;>
      simp only [pow_two, mul_assoc]
  have hthird := CoordinateBound.mul_through_three (hqs.pow 2) (hΓs 1 1) hU
    (by positivity : 0 ≤ 8 * (heightQuotientJetBound G Z d c)^2) hΓN hqsq (hΓb 1 1)
  have hb := CoordinateBound.add
    ((hΓs 0 0).sub (contDiffOn_const.mul (hqs.mul (hΓs 0 1))))
    ((hqs.pow 2).mul (hΓs 1 1)) hU
    (CoordinateBound.sub (hΓs 0 0) (contDiffOn_const.mul (hqs.mul (hΓs 0 1))) hU (hΓb 0 0) htwice) hthird
  have hconstant : christoffelJetBound G d + |(2 : ℝ)| *
      (8 * heightQuotientJetBound G Z d c * christoffelJetBound G d) +
      8 * (8 * (heightQuotientJetBound G Z d c)^2) * christoffelJetBound G d =
      heightAlongDJetBound G Z d c := by norm_num [heightAlongDJetBound] <;> ring
  rw [hconstant] at hb
  apply CoordinateBound.congr_on hU hb
  intro p hp
  change christoffelAlongD g p (hessianQuotient g z p) i =
    christoffel g i 0 0 p - 2 * (hessianQuotient g z p * christoffel g i 0 1 p) +
      (hessianQuotient g z p)^2 * christoffel g i 1 1 p
  rw [christoffelAlongD_eq hg hU hp]
  ring

theorem heightPFirst_coordinate_bound_one
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) U 4 G)
    (hzB : CoordinateBound z U 5 Z)
    (hdet : ∀ p ∈ U, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ U, c ≤ |covHessian g z p 1 1|) (i : Fin 2) :
    CoordinateBound (heightPFirst g z i) U 1 (heightPFirstBound G Z d c) := by
  have hne := LowQuotient.denominator_ne_zero hc hyy
  have hH := hessianJetBound_nonneg hG hZ hd
  have hΓ := christoffelJetBound_nonneg hG hd
  have hD := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hJ := heightEnergyFirstQuotientBound_nonneg hG hZ hd hc
  have hK := curvatureFirstBound_nonneg hG hd
  have hsH := covHessian_contDiffOn hg hU hz 1 1
  have hsJ := height_jetEnergy_first_contDiffOn hg hU hz i
  have hsG := darbouxG_contDiffOn hg hU hz hne
  have hsΓ := christoffel_contDiffOn hg hU i 1 1
  have hJB := height_jetEnergy_first_coordinate_bound hg hU hz hG hZ
    (fun a b => (hgB a b).mono (by norm_num) le_rfl) (hzB.mono (by norm_num) le_rfl) i
  have hHB := covHessian_coordinate_bound hg hU hz hG hZ hd hgB hzB hdet 1 1
  let N := 32 * G * Z + hessianJetBound G Z d
  have hN : 0 ≤ N := by dsimp [N] <;> positivity
  have hJN : 32 * G * Z ≤ N := by dsimp [N] <;> linarith
  have hHN : hessianJetBound G Z d ≤ N := by dsimp [N] <;> nlinarith [mul_nonneg hG hZ]
  have hdiv : CoordinateBound (fun p => coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) /
      covHessian g z p 1 1) U 3 (heightEnergyFirstQuotientBound G Z d c) := by
    intro ds hds p hp
    exact LowQuotient.quotient_bound_through_three hsJ hsH hU hN hc
      (hJB.mono le_rfl hJN) (hHB.mono le_rfl hHN) hyy ds hds hp
  have hGΓ := CoordinateBound.mul_through_three hsG hsΓ hU hD hΓ
    (darbouxG_coordinate_bound hg hU hz hG hZ hd hc hgB hzB hdet hyy)
    (christoffel_coordinate_bound hg hU hG hd hgB hdet i 1 1)
  have hsdiv := hsJ.div hsH hne
  have hbracket := CoordinateBound.add hsdiv (hsG.mul hsΓ) hU hdiv hGΓ
  have hmul := CoordinateBound.mul_through_one (gaussianCurvature_contDiffOn hg hU)
    (hsdiv.add (hsG.mul hsΓ)) hU hK
    (by positivity : 0 ≤ heightEnergyFirstQuotientBound G Z d c + 8 * darbouxGJetBound G Z d c * christoffelJetBound G d)
    (gaussianCurvature_coordinate_bound_one hg hU hG hd hgB hdet)
    (hbracket.mono (by norm_num) le_rfl)
  have hbs := height_christoffelAlongD_contDiffOn hg hU hz hne i
  have hb := CoordinateBound.add hbs ((gaussianCurvature_contDiffOn hg hU).mul (hsdiv.add (hsG.mul hsΓ))) hU
    ((height_christoffelAlongD_coordinate_bound hg hU hz hG hZ hd hc hgB hzB hdet hyy i).mono
      (by norm_num) le_rfl) hmul
  apply CoordinateBound.congr_on hU hb
  intro p hp
  change heightPFirst g z i p = christoffelAlongD g p (hessianQuotient g z p) i +
    gaussianCurvature g p *
      (coordPartial i (jetEnergy g p) (fun r => coordPartial r z p) / covHessian g z p 1 1 +
        darbouxG g z p * christoffel g i 1 1 p)
  rw [heightPFirst_eq hg hU hp (hne p hp) i]
  unfold darbouxG
  simp only [div_eq_mul_inv]
  ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_HeightCoefficientClosedBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem exists_open_low_height_coefficients
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) :
    ∃ V : Set Coord, IsOpen V ∧ modelSquare ⊆ V ∧ V ⊆ U ∧
      (∀ p ∈ V, covHessian g z p 1 1 ≠ 0) ∧
      CoordinateBound (hessianQuotient g z) modelSquare 3 (heightQuotientJetBound G Z d c) ∧
      CoordinateBound (heightEnergy g z) modelSquare 3 (heightEnergyJetBound G Z) ∧
      CoordinateBound (darbouxG g z) modelSquare 3 (darbouxGJetBound G Z d c) ∧
      (∀ i : Fin 2, CoordinateBound (heightPFirst g z i) modelSquare 1 (heightPFirstBound G Z d c)) ∧
      (∀ k i j : Fin 2, CoordinateBound (christoffel g k i j) modelSquare 3 (christoffelJetBound G d)) := by
  obtain ⟨V, hV, hSV, hVU, hVne, _, hqB⟩ :=
    exists_open_quotient_domain_with_closed_low_bounds hg hU hSU hz hG hZ hd hc hgB hzB hdet hyy
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun i j => (hg.1 i j).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  have hgV : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  have hgBI (i j : Fin 2) := (hgB i j).restrict_domain interior_subset
  have hzBI := hzB.restrict_domain interior_subset
  have hdI (p : Coord) (hp : p ∈ interior modelSquare) := hdet p (interior_subset hp)
  have hyyI (p : Coord) (hp : p ∈ interior modelSquare) := hyy p (interior_subset hp)
  refine ⟨V, hV, hSV, hVU, hVne, hqB, ?_, ?_, ?_, ?_⟩
  · apply CoordinateBound.of_modelSquare_interior (heightEnergy_contDiffOn hg hU hz) hU hSU
    exact heightEnergy_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ
      (fun i j => (hgBI i j).mono (by norm_num) le_rfl) (hzBI.mono (by norm_num) le_rfl)
  · apply CoordinateBound.of_modelSquare_interior
      (darbouxG_contDiffOn hgV hV (hz.mono hVU) hVne) hV hSV
    exact darbouxG_coordinate_bound hgI isOpen_interior (hz.mono hIU) hG hZ hd hc hgBI hzBI hdI hyyI
  · intro i
    apply CoordinateBound.of_modelSquare_interior
      (heightPFirst_contDiffOn hgV hV (hz.mono hVU) hVne i) hV hSV
    exact heightPFirst_coordinate_bound_one hgI isOpen_interior (hz.mono hIU) hG hZ hd hc hgBI hzBI hdI hyyI i
  · intro k i j
    apply CoordinateBound.of_modelSquare_interior (christoffel_contDiffOn hg hU k i j) hU hSU
    exact christoffel_coordinate_bound hgI isOpen_interior hG hd hgBI hdI k i j

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_HeightFlowUniformBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem exists_height_flow_uniform_coefficients
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy g z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)
    (hD : ∀ p ∈ modelSquare, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p) :
    ∃ Y : ℝ → ℝ → ℝ,
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, |Y s t - s| ≤ (1 : ℝ) / 50) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) ∧
      (∀ p ∈ capChartDomain,
        0 < capChartRho Y p ∧
        1 / Real.exp (2 * heightQuotientJetBound G Z d c) ≤ capChartRho Y p ∧
        capChartRho Y p ≤ 1 / Real.exp (-2 * heightQuotientJetBound G Z d c)) ∧
      ContDiffOn ℝ ∞ (heightChartG1 g z Y) capChartDomain ∧
      CoordinateBound (heightChartG1 g z Y) capChartDomain 1 (heightG1JetBound G Z d c) ∧
      (∀ p ∈ capChartDomain, heightG1Lower G Z d c e0 ≤ heightChartG1 g z Y p) ∧
      (∀ ell : ℕ,
        ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain ∧
        CoordinateBound (heightChartB g z Y ell) capChartDomain 1 (heightBJetBound G Z d c ell) ∧
        ContDiffOn ℝ ∞ (heightChartRemainder g z Y ell) capChartDomain ∧
        ∀ p ∈ capChartDomain,
          |heightChartRemainder g z Y ell p| ≤ heightRemainderBound G Z d c e0 ell ∧
          heightChartC g z Y ell p = ((ell : ℝ) + 1) * coordPartial 1 (heightChartA g z Y) p +
            heightChartA g z Y p * heightChartRemainder g z Y ell p) := by
  let M := heightQuotientJetBound G Z d c
  have hM : 0 ≤ M := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hM
  have hH := hessianJetBound_nonneg hG hZ hd
  have hDG := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hP := heightPFirstBound_nonneg hG hZ hd hc
  have hDE := heightDriftErrorBound_nonneg hG hZ hd hc
  obtain ⟨V, hV, hSV, hVU, hVne, hqB, hEB, hGB, hPB, hΓB⟩ :=
    exists_open_low_height_coefficients hg hU hSU hz hG hZ hd hc hgB hzB hdet hyy
  have hgV : SmoothPositiveOn g V :=
    ⟨fun i j => (hg.1 i j).mono hVU, fun p hp => hg.2 p (hVU hp)⟩
  have hzV := hz.mono hVU
  have hq := hessianQuotient_contDiffOn hgV hV hzV hVne
  have hGs := darbouxG_contDiffOn hgV hV hzV hVne
  have hq1 (i : Fin 2) (p : Coord) (hp : p ∈ modelSquare) : |coordPartial i (hessianQuotient g z) p| ≤ M :=
    hqB [i] (by norm_num) p hp
  have hq2 (i j : Fin 2) (p : Coord) (hp : p ∈ modelSquare) :
      |coordPartial i (coordPartial j (hessianQuotient g z)) p| ≤ M := hqB [i, j] (by norm_num) p hp
  have hq3 (i j k : Fin 2) (p : Coord) (hp : p ∈ modelSquare) :
      |coordPartial i (coordPartial j (coordPartial k (hessianQuotient g z))) p| ≤ M :=
    hqB [i, j, k] (by norm_num) p hp
  obtain ⟨Y, hY, _, hstart, hode, _, hdisp50, hrange, _⟩ := exists_cap_flow hq hV hSV hsmall
  have hconf (s : ℝ) (hs : s ∈ Icc (-2 : ℝ) 2) (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) 2) :
      Y s t ∈ Icc (-3 : ℝ) 3 := abs_le.mp ((hrange s hs t ht).1.trans (by norm_num))
  have hYs := cap_flow_joint_contDiffOn hq hV hSV hY hconf hstart hode
  have hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s := fun s hs t ht =>
    cap_flow_initial_deriv_pos hq hV hSV hY hconf hstart hode hs ht
  have hdisp' (p : Coord) (hp : p ∈ capChartDomain) : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50 :=
    hdisp50 (p 1) ⟨hp.2.1.le, hp.2.2.le⟩ (p 0) ⟨hp.1.1.le, hp.1.2.le⟩
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp' p hp)
  have hmapS : MapsTo (capChart Y) capChartDomain modelSquare := fun p hp => modelOpenSquare_subset (hmapO hp)
  have hmapV : MapsTo (capChart Y) capChartDomain V := fun p hp => hSV (hmapS hp)
  have hFB := capFlowHeight_coordinate_bound hq hV hSV hY hconf hstart hode hM hsmall hq1 hq2 hq3
  have hrec (p : Coord) (hp : p ∈ capChartDomain) :=
    capReciprocal_bounds_from_q hq hV hSV hY hconf hstart hode hM hsmall hq1 hq2 hq3 hp
  have hrhoL (p : Coord) (hp : p ∈ capChartDomain) : 1 / Real.exp (2 * M) ≤ capChartRho Y p :=
    capChartRho_lower_from_q hq hV hSV hY hconf hstart hode hM (hq1 1) hp
  have hrhoJ : 0 ≤ flowRhoJetBound M := by dsimp [flowRhoJetBound] <;> positivity
  have hrhoB : CoordinateBound (capChartRho Y) capChartDomain 1 (flowRhoJetBound M) := by
    intro ds hds p hp
    cases ds with
    | nil =>
      exact (hrec p hp).2.1.trans (by
        dsimp [flowRhoJetBound]
        have hterm : 0 ≤ flowCoordinateBound M / (Real.exp (-2 * M))^2 := by positivity
        linarith)
    | cons i ds =>
      cases ds with
      | nil =>
        exact ((hrec p hp).2.2.1 i).trans (by
          dsimp [flowRhoJetBound]
          have hterm : 0 ≤ 1 / Real.exp (-2 * M) := by positivity
          linarith)
      | cons _ ds => simp only [List.length_cons] at hds; omega
  have hrhos := capChartRho_contDiffOn hYs hvar
  have hGrho := capPullback_bound_one hYs hGs hV hmapV hmapS hDG hF
    (hGB.mono (by norm_num) le_rfl) hFB
  have hG1B := CoordinateBound.mul_through_one (capPullback_contDiffOn hYs hGs hmapV)
    (hrhos.mul hrhos) capChartDomain_isOpen (mul_nonneg hDG (by positivity))
    (by positivity : 0 ≤ 2 * flowRhoJetBound M * flowRhoJetBound M) hGrho
    (CoordinateBound.mul_through_one hrhos hrhos capChartDomain_isOpen hrhoJ hrhoJ hrhoB hrhoB)
  have hHB := covHessian_coordinate_bound_closed_square hg hU hSU hz hG hZ hd hgB hzB hdet 1 1
  have hGfloor (p : Coord) (hp : p ∈ capChartDomain) :
      e0 / (1 + hessianJetBound G Z d)^2 ≤ darbouxG g z (capChart Y p) :=
    darbouxG_lower_of_energy_floor g z _ he0 (hEfloor _ (hmapS hp)) hH
      (hHB [] (by norm_num) _ (hmapS hp)) (hVne _ (hmapV hp))
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hD0 := fun p (hp : p ∈ modelOpenSquare) => hD p (modelOpenSquare_subset hp)
  have hE0 := fun p (hp : p ∈ modelOpenSquare) => he0.trans_le (hEfloor p (modelOpenSquare_subset hp))
  have hyy0 := fun p (hp : p ∈ modelOpenSquare) => hVne p (hSV (modelOpenSquare_subset hp))
  refine ⟨Y, capChart_contDiffOn hYs, hY, hYs, hvar, hstart, hode, hconf, hdisp50, hdisp', ?_,
    (capPullback_contDiffOn hYs hGs hmapV).mul (hrhos.pow 2), ?_, ?_, ?_⟩
  · intro p hp
    exact ⟨(hrec p hp).1, hrhoL p hp, (le_abs_self _).trans (hrec p hp).2.1⟩
  · convert hG1B using 1 <;> first
      | (funext p; simp only [heightChartG1, pow_two])
      | (dsimp [heightG1JetBound, M]; ring)
  · intro p hp
    have hGL : 0 < e0 / (1 + hessianJetBound G Z d)^2 := by positivity
    have hGpos := hGL.trans_le (hGfloor p hp)
    have hsquare := pow_le_pow_left₀ (show 0 ≤ 1 / Real.exp (2 * M) by positivity) (hrhoL p hp) 2
    exact mul_le_mul (hGfloor p hp) hsquare (sq_nonneg _) hGpos.le
  · intro ell
    have hBB := heightOriginalB_bound_one hgV hV hSV hzV hVne (hPB 0) hqB ell
    refine ⟨heightChartB_contDiffOn hgV hV hzV hVne hYs hmapV ell, ?_,
      heightChartRemainder_contDiffOn hgO modelOpenSquare_isOpen hzO hyy0 hE0 hYs hvar hmapO ell, ?_⟩
    · exact capPullback_bound_one hYs (heightOriginalB_contDiffOn hgV hV hzV hVne ell) hV hmapV hmapS
        (by positivity : 0 ≤ heightPFirstBound G Z d c + 2 * (ell : ℝ) * M) hF hBB hFB
    · intro p hp
      refine ⟨?_, heightChartC_factor hgO modelOpenSquare_isOpen hzO hD0 hyy0 hE0 hYs hvar hmapO hp ell⟩
      exact heightChartRemainder_bound_of_low_coefficients g z Y p ell hDE hDG
        (show 0 ≤ flowCoordinateBound M / (Real.exp (-2 * M))^3 by positivity)
        (show 0 < e0 / (1 + hessianJetBound G Z d)^2 by positivity)
        (show 0 < 1 / Real.exp (2 * M) by positivity)
        (curvatureDriftError_bound_original_data hG hZ hc hgB hzB hEB hHB hΓB hyy hsmall (hmapS hp))
        (hGB [1] (by norm_num) _ (hmapS hp)) (hGfloor p hp) (hrhoL p hp) (hrec p hp).2.2.2.1

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_HeightPrincipalBounds
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Geometry
open SmoothLocal.Flow

theorem gaussianCurvature_coordinate_bound_one_closed
    {g : MetricField} {U : Set Coord} {G d : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hd : 0 < d)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|) :
    CoordinateBound (gaussianCurvature g) modelSquare 1 (curvatureFirstBound G d) := by
  have hIU : interior modelSquare ⊆ U := interior_subset.trans hSU
  have hgI : SmoothPositiveOn g (interior modelSquare) :=
    ⟨fun i j => (hg.1 i j).mono hIU, fun p hp => hg.2 p (hIU hp)⟩
  apply CoordinateBound.of_modelSquare_interior (gaussianCurvature_contDiffOn hg hU) hU hSU
  exact gaussianCurvature_coordinate_bound_one hgI isOpen_interior hG hd
    (fun i j => (hgB i j).restrict_domain interior_subset) (fun p hp => hdet p (interior_subset hp))

end SmoothLocal.Geometry

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem heightChartA_bound_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ) / 100)
    (hrho : ∀ p ∈ capChartDomain,
      1 / Real.exp (2 * heightQuotientJetBound G Z d c) ≤ capChartRho Y p)
    (hG1s : ContDiffOn ℝ ∞ (heightChartG1 g z Y) capChartDomain)
    (hG1B : CoordinateBound (heightChartG1 g z Y) capChartDomain 1 (heightG1JetBound G Z d c)) :
    CoordinateBound (heightChartA g z Y) capChartDomain 1 (heightAJetBound G Z d c) := by
  have hM := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hM
  have hK := curvatureFirstBound_nonneg hG hd
  have hG1 := heightG1JetBound_nonneg hG hZ hd hc
  have hmapU : MapsTo (capChart Y) capChartDomain U := fun p hp => hSU (hmapS hp)
  have hKs := gaussianCurvature_contDiffOn hg hU
  have hKB := capPullback_bound_one_from_partials hY hKs hU hmapU hmapS hK hF
    (gaussianCurvature_coordinate_bound_one_closed hg hU hSU hG hd hgB hdet)
    (fun i p hp => capFlowHeight_partial_bound_of_rho hY hvar hode hmapS hsmall hM hrho hp i)
  have hb := CoordinateBound.mul_through_one hG1s (capPullback_contDiffOn hY hKs hmapU)
    capChartDomain_isOpen hG1 (mul_nonneg hK (by positivity)) hG1B hKB
  exact CoordinateBound.congr_on capChartDomain_isOpen hb (fun p _ => heightChartA_eq g z Y p)

theorem heightChartB_primitive_bounds
    {g : MetricField} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {MB : ℝ} (ell : ℕ)
    (hB : ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain)
    (hBB : CoordinateBound (heightChartB g z Y ell) capChartDomain 1 MB)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |coordinatePrimitive (heightChartB g z Y ell) p| ≤ 2 * MB ∧
    |coordPartial 1 (coordinatePrimitive (heightChartB g z Y ell)) p| ≤ 2 * MB := by
  exact ⟨coordinatePrimitive_abs_bound hB.continuousOn (by norm_num : (0 : ℝ) < 2) hp
      (fun q hq => hBB [] (by norm_num) q hq),
    coordinatePrimitive_partial_s_bound hB (by norm_num : (0 : ℝ) < 2) hp
      (fun q hq => hBB [1] (by norm_num) q hq)⟩

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_HeightCapLowData
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem heightChartC_value_bound
    {g : MetricField} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (ell : ℕ)
    (hAB : CoordinateBound (heightChartA g z Y) capChartDomain 1 (heightAJetBound G Z d c))
    (hrB : ∀ p ∈ capChartDomain,
      |heightChartRemainder g z Y ell p| ≤ heightRemainderBound G Z d c e0 ell ∧
      heightChartC g z Y ell p = ((ell : ℝ)+1)*coordPartial 1 (heightChartA g z Y) p +
        heightChartA g z Y p*heightChartRemainder g z Y ell p)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |heightChartC g z Y ell p| ≤ heightCapCValueBound G Z d c e0 ell := by
  have hel : 0 ≤ (ell : ℝ)+1 := by positivity
  have hfirst := mul_le_mul_of_nonneg_left (hAB [1] (by norm_num) p hp) hel
  have hsecond :=
    (mul_le_mul_of_nonneg_left (hrB p hp).1 (abs_nonneg (heightChartA g z Y p))).trans
      (mul_le_mul_of_nonneg_right (hAB [] (by norm_num) p hp)
        (heightRemainderBound_nonneg hG hZ hd hc he0 ell))
  rw [(hrB p hp).2]
  calc
    _ ≤ |((ell : ℝ)+1)*coordPartial 1 (heightChartA g z Y) p| +
        |heightChartA g z Y p*heightChartRemainder g z Y ell p| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul,abs_of_nonneg hel,abs_mul]
      exact add_le_add hfirst hsecond

theorem heightChartB_primitive_first_bounds
    {g : MetricField} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ} {MB : ℝ} (ell : ℕ)
    (hMB : 0 ≤ MB) (hB : ContDiffOn ℝ ∞ (heightChartB g z Y ell) capChartDomain)
    (hBB : CoordinateBound (heightChartB g z Y ell) capChartDomain 1 MB)
    {p : Coord} (hp : p ∈ capChartDomain) :
    |coordinatePrimitive (heightChartB g z Y ell) p| ≤ 2*MB ∧
      ∀ i : Fin 2, |coordPartial i (coordinatePrimitive (heightChartB g z Y ell)) p| ≤ 2*MB := by
  obtain ⟨hIv,hIs⟩ := heightChartB_primitive_bounds ell hB hBB hp
  refine ⟨hIv,?_⟩
  intro i
  fin_cases i
  · simp only [Fin.mk_zero]
    rw [coordinatePrimitive_partial_t hB (by norm_num : (0 : ℝ) < 2) hp]
    exact (hBB [] (by norm_num) p hp).trans (by linarith only [hMB])
  · simpa only [Fin.mk_one] using hIs

theorem heightCurvaturePullback_bound_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ} {G Z d c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => g p i j) modelSquare 4 G)
    (hdet : ∀ p ∈ modelSquare, d ≤ |(g p).det|)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    (hmapS : MapsTo (capChart Y) capChartDomain modelSquare)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ)/100)
    (hrho : ∀ p ∈ capChartDomain, 1/Real.exp (2*heightQuotientJetBound G Z d c) ≤ capChartRho Y p) :
    CoordinateBound (capPullback Y (gaussianCurvature g)) capChartDomain 1 (heightCapCurvatureBound G Z d c) := by
  have hM := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hM
  have hK := curvatureFirstBound_nonneg hG hd
  exact capPullback_bound_one_from_partials hY (gaussianCurvature_contDiffOn hg hU) hU
    (fun p hp => hSU (hmapS hp)) hmapS hK hF
    (gaussianCurvature_coordinate_bound_one_closed hg hU hSU hG hd hgB hdet)
    (fun i p hp => capFlowHeight_partial_bound_of_rho hY hvar hode hmapS hsmall hM hrho hp i)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualHighEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem actualP_single_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : (![x, y] : Coord) ∈ U) (hyy : covHessian g z ![x, y] 1 1 ≠ 0)
    (n : ℕ) (hn : 2 ≤ n) :
    chainTerm (sixVariableP g) (solutionJetCurve z x) (ChainWord.single n) y =
      directLinearization g z (verticalJet z n) ![x, y] := by
  rw [chainTerm_single_eq]
  have h := fullBlockPartition_actual_linearization hg hU hz hp hyy n hn
  rw [fullBlockPartition_term] at h
  exact h

theorem actual_differentiated_Darboux
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {x y : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hp : (![x, y] : Coord) ∈ U) (m : ℕ) :
    coordPartial 0 (coordPartial 0 (verticalJet z (m + 3))) ![x, y] =
      directLinearization g z (verticalJet z (m + 3)) ![x, y] +
        (m + 3 : ℝ) * secondJetCorrection g z (verticalJet z (m + 3)) ![x, y] +
        actualHighRemainder g z m ![x, y] := by
  have heq : (fun t => coordPartial 0 (coordPartial 0 z) ![x, t]) =ᶠ[𝓝 y]
      sixVariableP g ∘ solutionJetCurve z x := by
    filter_upwards [(hU.preimage (verticalPoint_contDiff x).continuous).mem_nhds hp] with t ht
    change coordPartial 0 (coordPartial 0 z) ![x, t] = sixVariableP g (solutionJet z ![x, t])
    rw [sixVariableP_solutionJet]
    exact solvedDarboux_at_height hg hU hz ht (hyy _ ht) (hD _ ht)
  have htop := actualP_top_chain_expansion hg hU hz hyy hp m
  rw [← heq.iteratedDeriv_eq (m + 3)] at htop
  rw [verticalJet_slice hU (partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0)
      x (m + 3) y hp,
    verticalJet_two_coordPartials hU hz hp (m + 3) 0 0,
    actualP_single_linearization hg hU hz hp (hyy _ hp) (m + 3) (by omega),
    actualP_pair_extract_secondJet hg hU hz hyy hp (m + 2) (by omega),
    chainSum_eq_coordinateChainSum hU hz hp] at htop
  unfold actualHighRemainder
  convert htop using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem actual_differentiated_Darboux_at
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) {p : Coord} (hp : p ∈ U) :
    coordPartial 0 (coordPartial 0 (verticalJet z (m + 3))) p =
      directLinearization g z (verticalJet z (m + 3)) p +
        (m + 3 : ℝ) * secondJetCorrection g z (verticalJet z (m + 3)) p +
        actualHighRemainder g z m p := by
  have he : (![p 0, p 1] : Coord) = p := by
    ext i
    fin_cases i <;> rfl
  simpa only [he] using actual_differentiated_Darboux hg hU hz hD hyy
    (x := p 0) (y := p 1) (by simpa only [he] using hp) m

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_ActualHighDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.Weighted

theorem actual_differentiated_drift
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) {p : Coord} (hp : p ∈ U) :
    driftOperator (hessianQuotient g z) (heightOriginalA g z)
      (heightOriginalB g z (m + 3)) (heightOriginalC0 g z (m + 3))
      (verticalJet z (m + 3)) p = actualHighRemainder g z m p := by
  have hid := driftOperator_linearized_identity
    (hessianQuotient_contDiffOn hg hU hz hyy) (verticalJet_contDiffOn hU hz (m + 3))
    (heightOriginalA_contDiffOn hg hU hz hyy) hU hp
    (heightPFirst g z 0) (heightPFirst g z 1) (m + 3)
  have hC : (fun r => coordinateDrift (hessianQuotient g z) (hessianQuotient g z) r -
      heightPFirst g z 0 r * hessianQuotient g z r - heightPFirst g z 1 r +
      (m + 3 : ℝ) * coordPartial 1 (heightOriginalA g z) r) =
      heightOriginalC0 g z (m + 3) := by
    funext r
    simp only [heightOriginalC0, Nat.cast_add, Nat.cast_ofNat]
    ring
  simp only [Nat.cast_add, Nat.cast_ofNat] at hid
  rw [hC] at hid
  have hB : (fun r => -heightPFirst g z 0 r -
      2 * (m + 3 : ℝ) * coordPartial 1 (hessianQuotient g z) r) =
      heightOriginalB g z (m + 3) := by
    funext r
    simp only [heightOriginalB, Nat.cast_add, Nat.cast_ofNat]
  rw [hB] at hid
  rw [hid]
  have h := actual_differentiated_Darboux_at hg hU hz hD hyy m hp
  unfold directLinearization secondJetCorrection at h
  simp only [heightOriginalA] at *
  linarith only [h]

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_ActualFlowHighEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE SmoothLocal.Weighted

theorem actual_flow_high_equation
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hmap : MapsTo (capChart Y) capChartDomain U) (m : ℕ) {p : Coord}
    (hp : p ∈ capChartDomain) :
    multiplierOperator (heightChartA g z Y) (heightChartB g z Y (m + 3))
      (heightChartC g z Y (m + 3)) (capPullback Y (verticalJet z (m + 3))) p =
      capPullback Y (actualHighRemainder g z m) p := by
  rw [← height_coefficient_operator_transport hg hU hz hyy hY hode hvar hmap
    (verticalJet_contDiffOn hU hz (m + 3)) hp (m + 3)]
  exact actual_differentiated_drift hg hU hz hD hyy m (hmap hp)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedFarNegative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem heightChartA_negative_of_curvature
    (g : MetricField) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (p : Coord)
    {cG delta : ℝ} (hcG : 0 < cG) (hdelta : 0 < delta)
    (hG : cG ≤ heightChartG1 g z Y p)
    (hK : capPullback Y (gaussianCurvature g) p ≤ -delta) :
    heightChartA g z Y p ≤ -(cG * delta) := by
  rw [heightChartA_eq]
  have hGpos : 0 ≤ heightChartG1 g z Y p := (hcG.trans_le hG).le
  calc
    _ ≤ heightChartG1 g z Y p * (-delta) := mul_le_mul_of_nonneg_left hK hGpos
    _ ≤ cG * (-delta) := mul_le_mul_of_nonpos_right hG (by linarith)
    _ = _ := by ring

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_PatchFlowCoercivity
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

variable {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord}
variable {Y : ℝ → ℝ → ℝ} {p : Coord} {kappa : ℝ}

theorem patch_heightChartA_eventually_model
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hp : p ∈ capChartDomain) (hk : 0 < kappa) (hU : IsOpen U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (himage : capChart Y p ∈ U)
    (hsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤ kappa / 8) :
    heightChartA (g0 + eta) z Y =ᶠ[𝓝 p]
      (fun q => heightChartG1 (g0 + eta) z Y q * capModelCurvature kappa Y q) := by
  have heq := patch_capCurvature_eventually_model hY hp hk hU hbackground hsupport hcentral himage hsmall
  filter_upwards [heq] with q hq
  rw [heightChartA_eq, hq]

theorem patch_heightChart_near_principal_lower
    (hg : SmoothPositiveOn (g0 + eta) U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian (g0 + eta) z p 1 1 ≠ 0)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient (g0 + eta) z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hdisp : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      |Y s t - s| ≤ (1 : ℝ) / 50)
    (hqsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0 + eta) z p| ≤ (1 : ℝ) / 100)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (hp : p ∈ capChartDomain) (hs : p 1 ≤ 0) (ell : ℕ)
    {cG rhoMax epsilon MG : ℝ}
    (hkappa : 0 < kappa) (hcG : 0 < cG) (hG : cG ≤ heightChartG1 (g0 + eta) z Y p)
    (hrhoMax : capChartRho Y p ≤ rhoMax) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hsmall : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hGs : |coordPartial 1 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hGt : |coordPartial 0 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hKsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤
      modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell) :
    modelCoercivityMargin cG kappa rhoMax epsilon ell / 2 ≤
      directedPrincipal (heightChartA (g0 + eta) z Y) ell epsilon p := by
  have hK8 := hKsmall.trans (min_le_left _ _)
  have hKeq := patch_capCurvature_eventually_model hY hp hkappa hU hbackground hsupport hcentral
    (hmap hp) hK8
  have hAeq := patch_heightChartA_eventually_model (z := z) hY hp hkappa hU hbackground hsupport hcentral
    (hmap hp) hK8
  have hGsm : ContDiffOn ℝ ∞ (heightChartG1 (g0 + eta) z Y) capChartDomain :=
    (capPullback_contDiffOn hY (darbouxG_contDiffOn hg hU hz hyy) hmap).mul
      ((capChartRho_contDiffOn hY hvar).pow 2)
  have hGdiff := (hGsm.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hKmodel : |capModelCurvature kappa Y p| ≤
      modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell := by
    rw [← hKeq.self_of_nhds]
    exact hKsmall
  have hmodel := cap_model_full_principal_lower hY hode hvar hdisp hqsmall hp hs ell hGdiff
    hkappa hcG hG hrhoMax heps heps1 hsmall hGs hGt hKmodel
  have hprincipal : directedPrincipal (heightChartA (g0 + eta) z Y) ell epsilon p =
      directedPrincipal (fun q => heightChartG1 (g0 + eta) z Y q * capModelCurvature kappa Y q)
        ell epsilon p := by
    unfold directedPrincipal
    rw [coordPartial_eq_of_eventuallyEq hAeq 1, coordPartial_eq_of_eventuallyEq hAeq 0]
  rw [hprincipal]
  exact hmodel

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_PatchDirectedCoercivity
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

theorem patch_actual_directed_near_coercivity
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord}
    {Y : ℝ → ℝ → ℝ} {p : Coord} {kappa : ℝ}
    (hg : SmoothPositiveOn (g0 + eta) U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hDarboux : ∀ p ∈ U,
      (covHessian (g0 + eta) z p).det = gaussianCurvature (g0 + eta) p * heightEnergy (g0 + eta) z p)
    (hyy : ∀ p ∈ U, covHessian (g0 + eta) z p 1 1 ≠ 0)
    (hE : ∀ p ∈ U, 0 < heightEnergy (g0 + eta) z p)
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-hessianQuotient (g0 + eta) z (coordinatePoint t (Y s t)))
        (Icc (-2 : ℝ) 2) t)
    (hvar : ∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2,
      0 < deriv (fun r => Y r t) s)
    (hdisp : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      |Y s t - s| ≤ (1 : ℝ) / 50)
    (hqsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0 + eta) z p| ≤ (1 : ℝ) / 100)
    (hmap : MapsTo (capChart Y) capChartDomain U)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (hp : p ∈ capChartDomain) (hs : p 1 ≤ 0) (ell : ℕ)
    (cG rhoMax epsilon MG MI MB Mr MA MAs MG1 c1 D edge lambda : ℝ)
    (hkappa : 0 < kappa) (hcG : 0 < cG) (hG : cG ≤ heightChartG1 (g0 + eta) z Y p)
    (hrhoMax : capChartRho Y p ≤ rhoMax) (heps : 0 < epsilon) (heps1 : epsilon ≤ 1)
    (hqbudget : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax)
    (hGs : |coordPartial 1 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hGt : |coordPartial 0 (heightChartG1 (g0 + eta) z Y) p| ≤ MG)
    (hKsmall : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤
      modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell)
    (hedge : p 1 < edge) (hlambda : 0 < lambda)
    (hIs : |coordPartial 1 (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) p| ≤ MI)
    (hBp : |heightChartB (g0 + eta) z Y ell p| ≤ MB)
    (hr : |heightChartRemainder (g0 + eta) z Y ell p| ≤ Mr)
    (hAp : |heightChartA (g0 + eta) z Y p| ≤ MA)
    (hAs : |coordPartial 1 (heightChartA (g0 + eta) z Y) p| ≤ MAs)
    (hTbudget : 2 * (MI + epsilon + epsilon * 2 * MB) ≤ lambda)
    (hEbudget : (MI + 1 + 2 * MB) / 2 + Mr ≤ lambda / 8)
    (hcrossbudget : 4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 *
      epsilon^2 * MA ≤ 1 / 8)
    (hloss : (4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2) / lambda ≤
      modelCoercivityMargin cG kappa rhoMax epsilon ell / 8)
    (hGmax : heightChartG1 (g0 + eta) z Y p ≤ MG1)
    (hc1 : 0 ≤ c1) (hdist : edge - p 1 ≤ D)
    (hKstrip : capPullback Y (gaussianCurvature (g0 + eta)) p ≤ c1 * (edge - p 1))
    (hstripbudget : MG1 * c1 * (lambda * D + 8) ≤
      modelCoercivityMargin cG kappa rhoMax epsilon ell / 6)
    (x y : ℝ) :
    let A := heightChartA (g0 + eta) z Y
    let B := heightChartB (g0 + eta) z Y ell
    let C := heightChartC (g0 + eta) z Y ell
    let I := coordinatePrimitive B
    min (lambda / 8) (modelCoercivityMargin cG kappa rhoMax epsilon ell / 4) *
      directedWeight edge lambda I p * (x^2 + y^2) ≤
      multiplierT B (directedM edge lambda I) (directedN edge lambda epsilon I) p * x^2 +
        multiplierS A C (directedM edge lambda I) (directedN edge lambda epsilon I) p * y^2 +
        multiplierJ A B C (directedM edge lambda I) (directedN edge lambda epsilon I) p * x * y := by
  let mu := modelCoercivityMargin cG kappa rhoMax epsilon ell / 2
  have hmu : 0 < mu := div_pos
    (modelCoercivityMargin_pos ell hcG hkappa ((capChartRho_pos hY hvar hp).trans_le hrhoMax) heps)
    (by norm_num)
  have hA : DifferentiableAt ℝ (heightChartA (g0 + eta) z Y) p :=
    ((heightChartA_contDiffOn hg hU hz hyy hY hvar hmap).contDiffAt
      (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hB : ContDiffOn ℝ ∞ (heightChartB (g0 + eta) z Y ell) (coordinateRectangle 2 (-2) 2) :=
    heightChartB_contDiffOn hg hU hz hyy hY hmap ell
  have hC := heightChartC_factor hg hU hz hDarboux hyy hE hY hvar hmap hp ell
  have hprincipal : mu ≤ directedPrincipal (heightChartA (g0 + eta) z Y) ell epsilon p :=
    patch_heightChart_near_principal_lower hg hU hz hyy hY hode hvar hdisp hqsmall hmap
      hbackground hsupport hcentral hp hs ell hkappa hcG hG hrhoMax heps heps1 hqbudget hGs hGt hKsmall
  have hstrip : 0 < heightChartA (g0 + eta) z Y p →
      weightH0 edge lambda p * heightChartA (g0 + eta) z Y p ≤ mu / 3 := by
    intro hpositive
    rw [heightChartA_eq]
    apply actual_positive_curvature_strip_budget (sub_pos.mpr hedge) hdist hc1 hlambda.le
      (hcG.trans_le hG).le hGmax hKstrip
    dsimp only [mu]
    linarith
  have hloss' : (4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2) / lambda ≤
      mu / 4 := by dsimp only [mu] <;> linarith
  have hh := primitive_directed_near_coercivity hB (by norm_num : (0 : ℝ) < 2) hp
    (heightChartA (g0 + eta) z Y) (heightChartC (g0 + eta) z Y ell)
    (heightChartRemainder (g0 + eta) z Y ell) hA edge lambda epsilon ell hedge hlambda
    heps.le heps1 hC MI MB Mr MA MAs mu hmu hIs hBp hr hAp hAs hTbudget hEbudget hcrossbudget
    hloss' hprincipal hstrip x y
  have hm : mu / 2 = modelCoercivityMargin cG kappa rhoMax epsilon ell / 4 := by
    dsimp only [mu]
    ring
  rw [hm] at hh
  exact hh

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_UniformRichPatchFlow
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model

theorem exists_patch_uniform_numeric_directed_flow
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0 + eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => (g0 + eta) p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0 + eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0 + eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0 + eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0 + eta) z p| ≤ (1 : ℝ) / 100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0 + eta) z p).det = gaussianCurvature (g0 + eta) p * heightEnergy (g0 + eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0 + eta) p < -kappa / 2)
    (ell : ℕ) :
    let epsilon := heightDirectedEpsilon G Z d c e0 kappa ell
    let lambda := heightDirectedLambda G Z d c e0 kappa ell
    let c1 := heightDirectedSlope G Z d c e0 kappa ell
    let c2 := heightDirectedCoercivity G Z d c e0 kappa ell
    ∃ Y : ℝ → ℝ → ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) ∧
      (∀ s ∈ Ioo (-2 : ℝ) 2, ∀ t ∈ Ioo (-2 : ℝ) 2, 0 < deriv (fun r => Y r t) s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0 + eta) z (coordinatePoint t (Y s t)))
          (Icc (-2 : ℝ) 2) t) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) ∧
      ContDiffOn ℝ ∞ (heightChartA (g0 + eta) z Y) capChartDomain ∧
      ContDiffOn ℝ ∞ (heightChartB (g0 + eta) z Y ell) capChartDomain ∧
      ContDiffOn ℝ ∞ (heightChartC (g0 + eta) z Y ell) capChartDomain ∧
      ContDiffOn ℝ ∞ (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) capChartDomain ∧
      ContDiffOn ℝ ∞ (capPullback Y (gaussianCurvature (g0 + eta))) capChartDomain ∧
      ContDiffOn ℝ ∞ (heightChartG1 (g0 + eta) z Y) capChartDomain ∧
      (∀ p ∈ capChartDomain,
        heightG1Lower G Z d c e0 ≤ heightChartG1 (g0 + eta) z Y p ∧
        |coordinatePrimitive (heightChartB (g0 + eta) z Y ell) p| ≤ 2*heightBJetBound G Z d c ell ∧
        (∀ i : Fin 2, |coordPartial i (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) p| ≤
          heightCapCoefficientBound G Z d c e0 ell) ∧
        (∀ i : Fin 2, |coordPartial i (capPullback Y (gaussianCurvature (g0 + eta))) p| ≤
          heightCapCurvatureBound G Z d c) ∧
        |heightChartA (g0 + eta) z Y p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
        (∀ i : Fin 2, |coordPartial i (heightChartA (g0 + eta) z Y) p| ≤
          heightCapCoefficientBound G Z d c e0 ell) ∧
        |heightChartB (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
        |heightChartC (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell) ∧
      ∀ edge : ℝ, edge ≤ 0 → ∀ p ∈ capChartDomain, p 1 < edge →
        capPullback Y (gaussianCurvature (g0 + eta)) p ≤ c1 * (edge - p 1) →
        ∀ x y : ℝ,
          let A := heightChartA (g0 + eta) z Y
          let B := heightChartB (g0 + eta) z Y ell
          let C := heightChartC (g0 + eta) z Y ell
          let I := coordinatePrimitive B
          c2 * directedWeight edge lambda I p * (x^2 + y^2) ≤
            multiplierT B (directedM edge lambda I) (directedN edge lambda epsilon I) p * x^2 +
            multiplierS A C (directedM edge lambda I) (directedN edge lambda epsilon I) p * y^2 +
            multiplierJ A B C (directedM edge lambda I) (directedN edge lambda epsilon I) p * x * y := by
  let M := heightQuotientJetBound G Z d c
  let cG := heightG1Lower G Z d c e0
  let rhoMax := 1 / Real.exp (-2 * M)
  let MG := heightG1JetBound G Z d c
  let MB := heightBJetBound G Z d c ell
  let Mr := heightRemainderBound G Z d c e0 ell
  let MA := heightAJetBound G Z d c
  have hcG : 0 < cG := heightG1Lower_pos hG hZ hd he0
  have hrhoMax : 0 < rhoMax := by dsimp [rhoMax] <;> positivity
  have hMG : 0 ≤ MG := heightG1JetBound_nonneg hG hZ hd hc
  have hMB : 0 ≤ MB := heightBJetBound_nonneg hG hZ hd hc ell
  have hMr : 0 ≤ Mr := heightRemainderBound_nonneg hG hZ hd hc he0 ell
  have hMA : 0 ≤ MA := heightAJetBound_nonneg hG hZ hd hc
  let epsilon := heightDirectedEpsilon G Z d c e0 kappa ell
  let lambda := heightDirectedLambda G Z d c e0 kappa ell
  let c1 := heightDirectedSlope G Z d c e0 kappa ell
  obtain ⟨heps, heps1, hlambda, hc1, hqbudget, hTbudget, hEbudget,
      hcross, hloss, hfarbudget, hnearstrip, hstripbudget⟩ :=
    heightDirectedNumbers_spec ⟨hG,hZ,hd,hc,he0,hk⟩ ell
  let margin := modelCoercivityMargin cG kappa rhoMax epsilon ell
  let delta := modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell
  let c2 := min (lambda / 8) (margin / 4)
  have hmargin : 0 < margin := modelCoercivityMargin_pos ell hcG hk hrhoMax heps
  have hdelta : 0 < delta := modelPrincipalRadius_pos ell hcG hk hrhoMax heps (by norm_num) hMG
  have hc2 : 0 < c2 := by dsimp [c2] <;> positivity
  obtain ⟨Y, hchart, hYclosed, hYs, hvar, hstart, hode, hconf, hdisp50, hdisp,
      hrho, hG1s, hG1B, hGfloor, hall⟩ :=
    exists_height_flow_uniform_coefficients hg hU hSU hz hG hZ hd hc he0 hgB hzB hdet hyy hEfloor hsmall hD
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hmapS : MapsTo (capChart Y) capChartDomain modelSquare :=
    fun p hp => modelOpenSquare_subset (hmapO hp)
  have hAB := heightChartA_bound_one hg hU hSU hG hZ hd hc hgB hdet hYs hvar hode hmapS hsmall
    (fun p hp => (hrho p hp).2.1) hG1s hG1B
  obtain ⟨hBs, hBB, hrs, hrB⟩ := hall ell
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn (g0 + eta) modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU, fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hyyn := LowQuotient.denominator_ne_zero hc hyy
  have hyyO := fun p (hp : p ∈ modelOpenSquare) => hyyn p (modelOpenSquare_subset hp)
  have hEO := fun p (hp : p ∈ modelOpenSquare) => he0.trans_le (hEfloor p (modelOpenSquare_subset hp))
  have hDO := fun p (hp : p ∈ modelOpenSquare) => hD p (modelOpenSquare_subset hp)
  have hbackgroundO := fun p (hp : p ∈ modelOpenSquare) => hbackground p (hOU hp)
  have hAs := heightChartA_contDiffOn hgO modelOpenSquare_isOpen hzO hyyO hYs hvar hmapO
  have hKB := heightCurvaturePullback_bound_one hg hU hSU hG hZ hd hc hgB hdet
    hYs hvar hode hmapS hsmall (fun p hp => (hrho p hp).2.1)
  obtain ⟨hMF,hMFA,hMFI,hMFB,hMFC⟩ := heightCapCoefficientBound_dominates hG hZ hd hc he0 ell
  have hfixed (p : Coord) (hp : p ∈ capChartDomain) :
      heightG1Lower G Z d c e0 ≤ heightChartG1 (g0 + eta) z Y p ∧
      |coordinatePrimitive (heightChartB (g0 + eta) z Y ell) p| ≤ 2*heightBJetBound G Z d c ell ∧
      (∀ i : Fin 2, |coordPartial i (coordinatePrimitive (heightChartB (g0 + eta) z Y ell)) p| ≤
        heightCapCoefficientBound G Z d c e0 ell) ∧
      (∀ i : Fin 2, |coordPartial i (capPullback Y (gaussianCurvature (g0 + eta))) p| ≤
        heightCapCurvatureBound G Z d c) ∧
      |heightChartA (g0 + eta) z Y p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
      (∀ i : Fin 2, |coordPartial i (heightChartA (g0 + eta) z Y) p| ≤
        heightCapCoefficientBound G Z d c e0 ell) ∧
      |heightChartB (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell ∧
      |heightChartC (g0 + eta) z Y ell p| ≤ heightCapCoefficientBound G Z d c e0 ell := by
    obtain ⟨hIv,hIi⟩ := heightChartB_primitive_first_bounds ell hMB hBs hBB hp
    exact ⟨hGfloor p hp,hIv,fun i => (hIi i).trans hMFI,
      fun i => hKB [i] (by norm_num) p hp,
      (hAB [] (by norm_num) p hp).trans hMFA,
      fun i => (hAB [i] (by norm_num) p hp).trans hMFA,
      (hBB [] (by norm_num) p hp).trans hMFB,
      (heightChartC_value_bound hG hZ hd hc he0 ell hAB hrB hp).trans hMFC⟩
  refine ⟨Y, heps, heps1, hlambda, hc1, hc2, hchart, hYs, hvar, hstart, hode, hdisp,
    hAs, hBs, heightChartC_contDiffOn hgO modelOpenSquare_isOpen hzO hDO hyyO hEO hYs hvar hmapO ell,
    coordinatePrimitive_contDiffOn hBs,
    capPullback_contDiffOn hYs (gaussianCurvature_contDiffOn hg hU) (fun p hp => hSU (hmapS hp)),
    hG1s,hfixed, ?_⟩
  intro edge hedge0 p hp hedge hKstrip x y
  have hs : p 1 ≤ 0 := (le_of_lt hedge).trans hedge0
  have hdist : edge - p 1 ≤ 2 := by linarith [hp.2.1]
  have hI := (heightChartB_primitive_bounds ell hBs hBB hp).2
  have hBpoint : |heightChartB (g0 + eta) z Y ell p| ≤ MB := hBB [] (by norm_num) p hp
  have hrpoint : |heightChartRemainder (g0 + eta) z Y ell p| ≤ Mr := (hrB p hp).1
  have hApoint : |heightChartA (g0 + eta) z Y p| ≤ MA := hAB [] (by norm_num) p hp
  have hAspoint : |coordPartial 1 (heightChartA (g0 + eta) z Y) p| ≤ MA := hAB [1] (by norm_num) p hp
  have hAtpoint : |coordPartial 0 (heightChartA (g0 + eta) z Y) p| ≤ MA := hAB [0] (by norm_num) p hp
  have hGspoint : |coordPartial 1 (heightChartG1 (g0 + eta) z Y) p| ≤ MG := hG1B [1] (by norm_num) p hp
  have hGtpoint : |coordPartial 0 (heightChartG1 (g0 + eta) z Y) p| ≤ MG := hG1B [0] (by norm_num) p hp
  have hGmax : heightChartG1 (g0 + eta) z Y p ≤ MG := (le_abs_self _).trans (hG1B [] (by norm_num) p hp)
  by_cases hnear : |capPullback Y (gaussianCurvature (g0 + eta)) p| ≤ delta
  · exact patch_actual_directed_near_coercivity hgO modelOpenSquare_isOpen hzO hDO hyyO hEO
      hYs hode hvar hdisp50 hsmall hmapO hbackgroundO hsupport hcentral hp hs ell
      cG rhoMax epsilon MG (2 * MB) MB Mr MA MA MG c1 2 edge lambda hk hcG (hGfloor p hp)
      (hrho p hp).2.2 heps heps1 hqbudget hGspoint hGtpoint hnear hedge hlambda hI hBpoint hrpoint
      hApoint hAspoint hTbudget hEbudget hcross hloss hGmax hc1.le hdist hKstrip hstripbudget x y
  · have hKupper : capPullback Y (gaussianCurvature (g0 + eta)) p ≤ delta :=
      hKstrip.trans ((mul_le_mul_of_nonneg_left hdist hc1.le).trans hnearstrip)
    have hKnegative : capPullback Y (gaussianCurvature (g0 + eta)) p ≤ -delta := by
      by_contra hneg
      exact hnear (abs_le.mpr ⟨(lt_of_not_ge hneg).le, hKupper⟩)
    have hAfar := heightChartA_negative_of_curvature (g0 + eta) z Y p hcG hdelta (hGfloor p hp) hKnegative
    have hloss' :
        (4 * (2 * ((ell : ℝ) * MA + MA * Mr + MA * (2 * MB) + 1))^2 * epsilon^2) / lambda ≤
          (margin / 2) / 4 := by
      calc
        _ ≤ margin / 8 := hloss
        _ = _ := by ring
    have hh := primitive_directed_farnegative_coercivity hBs (by norm_num : (0 : ℝ) < 2) hp
      (heightChartA (g0 + eta) z Y) (heightChartC (g0 + eta) z Y ell)
      (heightChartRemainder (g0 + eta) z Y ell)
      ((hAs.contDiffAt (capChartDomain_isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      edge lambda epsilon ell hedge hlambda heps.le heps1 (hrB p hp).2
      (2 * MB) MB Mr MA MA MA (margin / 2) (cG * delta) (by positivity)
      hI hBpoint hrpoint hApoint hAspoint hTbudget hEbudget hcross hloss' hAtpoint
      (mul_pos hcG hdelta) hAfar hfarbudget x y
    have hhalf : (margin / 2) / 2 = margin / 4 := by ring
    rw [hhalf] at hh
    exact hh

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_UniformOriginalDataCapEstimate
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem exists_uniform_original_data_actual_high_cap_estimate
    {g0 eta : MetricField} {z : Coord → ℝ} {U : Set Coord} {G Z d c e0 kappa : ℝ}
    (hg : SmoothPositiveOn (g0+eta) U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hz : ContDiffOn ℝ ∞ z U) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0)
    (hgB : ∀ i j : Fin 2, CoordinateBound (fun p => (g0+eta) p i j) modelSquare 4 G)
    (hzB : CoordinateBound z modelSquare 5 Z)
    (hdet : ∀ p ∈ modelSquare, d ≤ |((g0+eta) p).det|)
    (hyy : ∀ p ∈ modelSquare, c ≤ |covHessian (g0+eta) z p 1 1|)
    (hEfloor : ∀ p ∈ modelSquare, e0 ≤ heightEnergy (g0+eta) z p)
    (hsmall : ∀ p ∈ modelSquare, |hessianQuotient (g0+eta) z p| ≤ (1 : ℝ)/100)
    (hD : ∀ p ∈ modelSquare,
      (covHessian (g0+eta) z p).det = gaussianCurvature (g0+eta) p*heightEnergy (g0+eta) z p)
    (hk : 0 < kappa)
    (hbackground : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p)
    (hsupport : tsupport eta ⊆ patchBox)
    (hcentral : ∀ p ∈ centralBox, gaussianCurvature (g0+eta) p < -kappa/2) (m : ℕ) :
    let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
    let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
    let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
    let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
    ∃ Y : ℝ → ℝ → ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧ 0 < c2 ∧
      ContDiffOn ℝ ∞ (capChart Y) capChartDomain ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s) ∧
      (∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
        HasDerivWithinAt (Y s) (-hessianQuotient (g0+eta) z (coordinatePoint t (Y s t)))
          (Icc (-2 : ℝ) 2) t) ∧
      (∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50) ∧
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
            (capPullback Y (verticalJet z (m+3))) (capPullback Y (actualHighRemainder (g0+eta) z m)) := by
  let epsilon := heightDirectedEpsilon G Z d c e0 kappa (m+3)
  let lambda := heightDirectedLambda G Z d c e0 kappa (m+3)
  let c1 := heightDirectedSlope G Z d c e0 kappa (m+3)
  let c2 := heightDirectedCoercivity G Z d c e0 kappa (m+3)
  obtain ⟨Y,heps,heps1,hlambda,hc1,hc2,hchart,hYs,hvar,hstart,hode,hdisp,
      hAs,hBs,hCs,hIs,hKs,hG1s,hfixed,hcoercive⟩ :=
    exists_patch_uniform_numeric_directed_flow hg hU hSU hz hG hZ hd hc he0 hgB hzB hdet hyy hEfloor
      hsmall hD hk hbackground hsupport hcentral (m+3)
  let g := g0+eta
  let u := capPullback Y (verticalJet z (m+3))
  let f := capPullback Y (actualHighRemainder g z m)
  let G1 := heightChartG1 g z Y
  let K := capPullback Y (gaussianCurvature g)
  let A := heightChartA g z Y
  let B := heightChartB g z Y (m+3)
  let C := heightChartC g z Y (m+3)
  let I := coordinatePrimitive B
  let M := heightCapCoefficientBound G Z d c e0 (m+3)
  let MK := heightCapCurvatureBound G Z d c
  let MI := 2*heightBJetBound G Z d c (m+3)
  let glow := heightG1Lower G Z d c e0
  have hM : 0 ≤ M := (heightCapCoefficientBound_dominates hG hZ hd hc he0 (m+3)).1
  have hMK : 0 ≤ MK := heightCapCurvatureBound_nonneg hG hZ hd hc
  have hglow : 0 < glow := heightG1Lower_pos hG hZ hd he0
  have hOU : modelOpenSquare ⊆ U := modelOpenSquare_subset.trans hSU
  have hgO : SmoothPositiveOn g modelOpenSquare :=
    ⟨fun i j => (hg.1 i j).mono hOU,fun p hp => hg.2 p (hOU hp)⟩
  have hzO := hz.mono hOU
  have hmapO : MapsTo (capChart Y) capChartDomain modelOpenSquare :=
    fun p hp => capChart_mem_modelOpenSquare hp (hdisp p hp)
  have hyyO : ∀ p ∈ modelOpenSquare, covHessian g z p 1 1 ≠ 0 :=
    fun p hp => LowQuotient.denominator_ne_zero hc hyy p (modelOpenSquare_subset hp)
  have hu : ContDiffOn ℝ ∞ u capChartDomain := capPullback_contDiffOn hYs
    (verticalJet_contDiffOn modelOpenSquare_isOpen hzO (m+3)) hmapO
  have hPDE (p : Coord) (hp : p ∈ capChartDomain) : multiplierOperator A B C u p = f p :=
    actual_flow_high_equation hgO modelOpenSquare_isOpen hzO
      (fun p hp => hD p (modelOpenSquare_subset hp)) hyyO hYs hode hvar hmapO m hp
  have hAeq : A = (fun q => G1 q*K q) := by
    funext q
    exact heightChartA_eq g z Y q
  have hPDERaw : ∀ p ∈ capChartDomain, multiplierOperator (fun q => G1 q*K q) B C u p = f p := by
    intro p hp
    rw [←hAeq]
    exact hPDE p hp
  refine ⟨Y,heps,heps1,hlambda,hc1,hc2,hchart,hstart,hode,hdisp,hPDE,?_⟩
  intro L R bottom top b hL hR hbottom hLR hbt htop hb
  let T := closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
  let S := closedRectangle L R bottom top
  let D := capDistanceBound bottom b
  let COverlap := capOverlapEnergyCost L R bottom b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R bottom b kappa c1 glow MK M
  let RHS := (((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6)*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (f p)^2)) +
    ((COverlap*(D^6+HElliptic))*
      rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b (fun p => (u p)^2))
  have hT : T ⊆ capChartDomain := capOuterRectangle_subset_domain hL hR hbottom (by linarith)
  have hS : S ⊆ capChartDomain := by
    intro p hp
    exact ⟨⟨hL.trans_le hp.1.1,hp.1.2.trans_lt hR⟩,
      ⟨hbottom.trans_le hp.2.1,by linarith [hp.2.2]⟩⟩
  have hcoerceClosed (p : Coord) (hp : p ∈ T) (hK : K p ≤ c1*edgeDistance b p) :
      c2*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
        multiplierQuadratic (fun q => G1 q*K q) B C (directedM b lambda I) (directedN b lambda epsilon I) u p := by
    rw [←hAeq]
    by_cases hedge : p 1 < b
    · have hh := hcoercive b hb p (hT hp) hedge hK (coordPartial 0 u p) (coordPartial 1 u p)
      unfold multiplierQuadratic
      convert hh using 1
    · have heq : p 1 = b := le_antisymm hp.2.2 (le_of_not_gt hedge)
      rw [directedWeight_edge_zero b lambda I p heq,
        directedQuadratic_edge_zero A B C I u b lambda epsilon p
          ((hAs.contDiffAt (capChartDomain_isOpen.mem_nhds (hT hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
          ((hIs.contDiffAt (capChartDomain_isOpen.mem_nhds (hT hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) heq]
      simp
  have hlow (p : Coord) (hp : p ∈ T) := hfixed p (hT hp)
  have hAvRaw (p : Coord) (hp : p ∈ T) : |G1 p*K p| ≤ M := by
    rw [←heightChartA_eq g z Y p]
    exact (hlow p hp).2.2.2.2.1
  have hAiRaw (p : Coord) (hp : p ∈ T) (i : Fin 2) : |coordPartial i (fun q => G1 q*K q) p| ≤ M := by
    rw [←hAeq]
    exact (hlow p hp).2.2.2.2.2.1 i
  have hi : (c2/2)*rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
      (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) ≤ RHS :=
    actual_cap_integrated_overlap_estimate hL hR hbottom (hbt.trans htop.le) hb hk hc1 hc2 hglow hM hMK
      hlambda.le heps.le heps1 hKs hG1s hBs hCs hIs hu hPDERaw hbackground hsupport
      (fun p hp => hOU (hmapO (hT hp))) (fun p hp => hdisp p (hT hp))
      (fun p hp => (hlow p hp).2.1) (fun p hp => (hlow p hp).2.2.1)
      (fun p hp => (hlow p hp).1) hAvRaw hAiRaw
      (fun p hp => (hlow p hp).2.2.2.2.2.2.1) (fun p hp => (hlow p hp).2.2.2.2.2.2.2)
      (fun p hp => (hlow p hp).2.2.2.1) hcoerceClosed
  have hinterior := capInterior_gradient_le_directed_energy hL hR hbottom hLR hbt htop hb
    hlambda.le hIs hu (fun p hp => (hfixed p (hS hp)).2.1)
  have hWpos : 0 < capInteriorWeightFloor top b lambda MI := capInteriorWeightFloor_pos htop
  have hden : 0 < c2/2 := by positivity
  have henergy : rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
      (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) ≤ (2/c2)*RHS := by
    have hh : rectangleIntegral (capOuterLeft L) (capOuterRight R) (capOuterBottom bottom) b
        (directedGradientEnergy (capSpatialCutoff L R bottom) I u b lambda) ≤ RHS/(c2/2) :=
      (le_div_iff₀ hden).mpr (by simpa only [mul_comm] using hi)
    have hscale (value : ℝ) : value/(c2/2) = (2/c2)*value := by
      rw [div_div_eq_mul_div, div_mul_eq_mul_div, mul_comm]
    rw [hscale RHS] at hh
    exact hh
  have hfinal := hinterior.trans (mul_le_mul_of_nonneg_left henergy (by positivity))
  change rectangleIntegral L R bottom top (fun p => (coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤ _
  have hscale : (1/capInteriorWeightFloor top b lambda MI)*(2/c2) =
      2/(c2*capInteriorWeightFloor top b lambda MI) := by
    rw [div_mul_div_comm, one_mul, mul_comm (capInteriorWeightFloor top b lambda MI)]
  calc
    _ ≤ (1/capInteriorWeightFloor top b lambda MI)*((2/c2)*RHS) := hfinal
    _ = (2/(c2*capInteriorWeightFloor top b lambda MI))*RHS := by rw [←mul_assoc,hscale]
    _ = _ := rfl

end SmoothLocal.Flow

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

theorem coordinateChainCoefficient_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (w : ChainWord) (r : Fin w.arity → Fin 6) :
    ContinuousOn (coordinateChainCoefficient g z w r) U := by
  intro p hp
  have hP := sixVariableP_contDiffAt_solutionJet hg hU hp (hyy p hp)
  have houter := (hP.differentiableAt_iteratedFDeriv (m := w.arity)
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl w.arity)).continuousAt
  have hjet := ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp)).continuousAt
  have heval := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin w.arity => DarbouxState) ℝ
    (fun i => Pi.single (r i) (1 : ℝ))).continuous.continuousAt
      (x := iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p))
  exact ((heval.comp houter).comp hjet).continuousWithinAt

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_MixedDarbouxElimination
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry

theorem actualP_mixed_faaExpansion
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    (k : ℕ) (v : Fin k → Coord) :
    iteratedFDeriv ℝ k (sixVariableP g ∘ solutionJet z) p v =
      ∑ c : OrderedFinpartition k, mixedFaaTerm g z v c p := by
  have h := congrArg (fun L => L v) (iteratedFDeriv_comp
    (sixVariableP_contDiffAt_solutionJet hg hU hp hyy)
    ((solutionJet_contDiffOn hU hz).contDiffAt (hU.mem_nhds hp))
    (le_of_lt (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)))
  simpa [FormalMultilinearSeries.taylorComp, ftaylorSeries,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, mixedFaaTerm] using h

theorem mixed_fullBlock_linearization
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hp : p ∈ U) (hyy : covHessian g z p 1 1 ≠ 0)
    {k : ℕ} (hk : 2 ≤ k) (v : Fin k → Coord) :
    mixedFaaTerm g z v (fullBlockPartition k (by omega)) p =
      heightPFirst g z 0 p * iteratedFDeriv ℝ k (coordPartial 0 z) p v +
      heightPFirst g z 1 p * iteratedFDeriv ℝ k (coordPartial 1 z) p v +
      2 * hessianQuotient g z p *
        iteratedFDeriv ℝ k (coordPartial 0 (coordPartial 1 z)) p v -
      ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
        iteratedFDeriv ℝ k (coordPartial 1 (coordPartial 1 z)) p v := by
  rw [mixed_fullBlock_term, solutionJet_fullJet_ge_two hU hz hp k hk v]
  rw [sixVariableP_vertical_direction hg hU hp hyy _ (by rfl) (by rfl)]
  rfl

theorem actualDarboux_mixed_principal
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U)
    {k : ℕ} (hk : 2 ≤ k) (v : Fin k → Coord) :
    iteratedFDeriv ℝ k (coordPartial 0 (coordPartial 0 z)) p v =
      2 * hessianQuotient g z p *
        iteratedFDeriv ℝ k (coordPartial 0 (coordPartial 1 z)) p v -
      ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
        iteratedFDeriv ℝ k (coordPartial 1 (coordPartial 1 z)) p v +
      mixedFaaRemainder g z (by omega) v p := by
  classical
  have heq : coordPartial 0 (coordPartial 0 z) =ᶠ[𝓝 p] sixVariableP g ∘ solutionJet z := by
    filter_upwards [hU.mem_nhds hp] with q hq
    change coordPartial 0 (coordPartial 0 z) q = sixVariableP g (solutionJet z q)
    rw [sixVariableP_solutionJet]
    exact solvedDarboux_at_height hg hU hz hq (hyy q hq) (hD q hq)
  have hder := congrArg (fun L => L v) ((heq.iteratedFDeriv ℝ k).self_of_nhds)
  have hfaa := actualP_mixed_faaExpansion hg hU hz hp (hyy p hp) k v
  have hsplit := (Finset.add_sum_erase (Finset.univ : Finset (OrderedFinpartition k))
    (fun c => mixedFaaTerm g z v c p) (Finset.mem_univ (fullBlockPartition k (by omega)))).symm
  rw [mixed_fullBlock_linearization hg hU hz hp (hyy p hp) hk v] at hsplit
  have hfull := hder.trans (hfaa.trans hsplit)
  calc
    _ = _ := hfull
    _ = _ := by unfold mixedFaaRemainder; ring

theorem actualDarboux_ordered_mixed_elimination
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p * heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (hp : p ∈ U)
    (ds : List (Fin 2)) (hds : 2 ≤ ds.length) :
    iteratedCoordPartial (ds ++ [0, 0]) z p =
      2 * hessianQuotient g z p * iteratedCoordPartial (ds ++ [0, 1]) z p -
      ((hessianQuotient g z p)^2 + gaussianCurvature g p * darbouxG g z p) *
        iteratedCoordPartial (ds ++ [1, 1]) z p +
      mixedFaaRemainder g z (by omega) (coordinateDirections ds) p := by
  have h := actualDarboux_mixed_principal hg hU hz hD hyy hp hds (coordinateDirections ds)
  have hxx := partial_contDiffOn (partial_contDiffOn hz hU 0) hU 0
  have hxy := partial_contDiffOn (partial_contDiffOn hz hU 1) hU 0
  have hyyS := partial_contDiffOn (partial_contDiffOn hz hU 1) hU 1
  rw [← iteratedCoordPartial_eq_jet hxx hU ds hp,
    ← iteratedCoordPartial_eq_jet hxy hU ds hp,
    ← iteratedCoordPartial_eq_jet hyyS hU ds hp] at h
  rw [orderedPartial_append ds [0, 0], orderedPartial_append ds [0, 1],
    orderedPartial_append ds [1, 1]]
  exact h

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QMetricDensityDecomposition
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

def qMetricFirstError (gTau gStar : MetricField) (w : DarbouxState) : ℝ :=
  curvatureDensity gTau (statePoint w)*(qMetricDensityFactor gTau w-qMetricDensityFactor gStar w)+
    (qMetricFirstLower gTau w-qMetricFirstLower gStar w)

theorem qMetricDensityFactor_at_height {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) :
    qMetricDensityFactor g (qSolutionJet z p) = 2*forcingCoefficient g z p := by
  unfold qMetricDensityFactor
  rw [stateQDenominator_qSolutionJet]
  unfold stateEnergy
  rw [statePoint_qSolutionJet,stateGradient_qSolutionJet,jetEnergy_at_height hg hp z,
    forcingCoefficient_eq_energy hg z hp]
  have hdet := metricDet_ne_zero hg hp
  field_simp [hdet,hxx]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_ActualRemainderL2
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

theorem firstJetPairRemainder_continuousOn
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (n : ℕ) :
    ContinuousOn (firstJetPairRemainder g z n) U := by
  have h0 := (partial_contDiffOn (heightPFirst_contDiffOn hg hU hz hyy 0) hU 1).continuousOn
  have h1 := (partial_contDiffOn (heightPFirst_contDiffOn hg hU hz hyy 1) hU 1).continuousOn
  exact (h0.mul (heightStateFactor_contDiffOn hU hz n 0).continuousOn).add
    (h1.mul (heightStateFactor_contDiffOn hU hz n 1).continuousOn)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_MixedRemainderFactors
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

theorem mixedFaaTerm_continuousOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    {k : ℕ} (v : Fin k → Coord) (c : OrderedFinpartition k) :
    ContinuousOn (mixedFaaTerm g z v c) U := by
  have hm (r : Fin c.length → Fin 6) : ContinuousOn
      (fun p => coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
        ∏ j, mixedFaaFactor z v c r j p) U :=
    (coordinateChainCoefficient_continuousOn hg hU hz hyy ⟨c.length, c.partSize⟩ r).mul
      (continuousOn_finsetProd Finset.univ
        (fun index _ => mixedFaaFactor_continuousOn hU hz v c r index))
  exact (continuousOn_finsetSum Finset.univ (fun indices _ => hm indices)).congr
    (fun point _ => mixedFaaTerm_scalar_expansion g z v c point)

theorem heightPFirst_abs_le_fullP_one
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : p ∈ U)
    (hyy : covHessian g z p 1 1 ≠ 0) (i : Fin 2) :
    |heightPFirst g z i p| ≤ ‖iteratedFDeriv ℝ 1 (sixVariableP g) (solutionJet z p)‖ := by
  have h := (fderiv ℝ (sixVariableP g) (solutionJet z p)).le_opNorm
    (Pi.single (gradientStateIndex i) (1 : ℝ))
  simpa only [sixVariableP_gradient_axis_at_height hg hU hp hyy, Pi.norm_single, norm_one,
    mul_one, Real.norm_eq_abs, norm_iteratedFDeriv_one] using h

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MixedRemainderL2
attribute [-instance] _root_.OAI.SmoothLocal.Geometry.instCountablePatchAddress
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.qToPStateCLM_apply _root_.OAI.SmoothLocal.HighEquation.qToPState_five _root_.OAI.SmoothLocal.HighEquation.qToPState_four _root_.OAI.SmoothLocal.HighEquation.qToPState_involutive _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState _root_.OAI.SmoothLocal.HighEquation.stateSegment_one _root_.OAI.SmoothLocal.HighEquation.stateSegment_zero _root_.OAI.SmoothLocal.Pulse.inverseShearCLM_apply
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

theorem mixedFaaRemainder_continuousOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    {k : ℕ} (hk : 0 < k) (v : Fin k → Coord) :
    ContinuousOn (mixedFaaRemainder g z hk v) U :=
  (((heightPFirst_contDiffOn hg hU hz hyy 0).continuousOn.mul
      (fullJet_fixed_input_continuousOn (partial_contDiffOn hz hU 0) hU k v)).add
    ((heightPFirst_contDiffOn hg hU hz hyy 1).continuousOn.mul
      (fullJet_fixed_input_continuousOn (partial_contDiffOn hz hU 1) hU k v))).add
    (continuousOn_finsetSum (Finset.univ.erase (fullBlockPartition k hk))
      (fun c _ => mixedFaaTerm_continuousOn hg hU hz hyy v c))

theorem mixedFaaTerm_eLpNorm_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 5 ≤ ds.length) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hP : ∀ n ≤ ds.length, ∀ p ∈ V, ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞))
    (c : OrderedFinpartition ds.length) (hc : c ≠ fullBlockPartition ds.length (by omega)) :
    eLpNorm (mixedFaaTerm g z (coordinateDirections ds) c) 2 (volume.restrict V) ≤
      chainWordL2Budget C B H V ds.length ⟨c.length, c.partSize⟩ := by
  classical
  have hcoeff (r : Fin c.length → Fin 6) (p : Coord) (hp : p ∈ V) :
      |coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p| ≤ C :=
    (coordinateChainCoefficient_abs_le_full_derivative g z ⟨c.length, c.partSize⟩ r p).trans
      (hP c.length c.length_le p hp)
  have hm (r : Fin c.length → Fin 6) : AEStronglyMeasurable
      (fun p => coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
        ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p) (volume.restrict V) :=
    (((coordinateChainCoefficient_continuousOn hg hU hz hyy ⟨c.length, c.partSize⟩ r).mul
      (continuousOn_finsetProd Finset.univ
        (fun j _ => mixedFaaFactor_continuousOn hU hz (coordinateDirections ds) c r j))).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hterm (r : Fin c.length → Fin 6) :
      eLpNorm (fun p => coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
        ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p) 2 (volume.restrict V) ≤
        ‖C‖ₑ * chainProductL2Budget B H V ds.length :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable hV hC (hcoeff r) (hm r)).trans
      (mul_le_mul' le_rfl (mixed_product_eLpNorm_two hU hz hV hVU ds hds hB hlow hheight c hc r))
  have he : mixedFaaTerm g z (coordinateDirections ds) c = fun p =>
      ∑ r : Fin c.length → Fin 6,
        coordinateChainCoefficient g z ⟨c.length, c.partSize⟩ r p *
          ∏ j, mixedFaaFactor z (coordinateDirections ds) c r j p :=
    funext (mixedFaaTerm_scalar_expansion g z (coordinateDirections ds) c)
  rw [he]
  exact finite_sum_eLpNorm_two Finset.univ _
    (fun _ => ‖C‖ₑ * chainProductL2Budget B H V ds.length)
    (fun r _ => hm r) (fun r _ => hterm r)

theorem mixedFaaRemainder_eLpNorm_two
    {g : MetricField} {z : Coord → ℝ} {U V : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0)
    (hV : MeasurableSet V) (hVU : V ⊆ U)
    (ds : List (Fin 2)) (hds : 5 ≤ ds.length) {C B : ℝ} (hC : 0 ≤ C) (hB : 1 ≤ B) {H : ℝ≥0}
    (hP : ∀ n ≤ ds.length, ∀ p ∈ V, ‖iteratedFDeriv ℝ n (sixVariableP g) (solutionJet z p)‖ ≤ C)
    (hlow : CoordinateBound z V (ds.length - 1) B)
    (hheight : ∀ es : List (Fin 2), es.length ≤ ds.length + 1 →
      eLpNorm (iteratedCoordPartial es z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) :
    eLpNorm (mixedFaaRemainder g z (by omega) (coordinateDirections ds)) 2 (volume.restrict V) ≤
      mixedRemainderL2Budget C B H V ds.length := by
  classical
  let s := (Finset.univ : Finset (OrderedFinpartition ds.length)).erase (fullBlockPartition ds.length (by omega))
  let f0 : Coord → ℝ := fun p => heightPFirst g z 0 p * iteratedCoordPartial (ds ++ [0]) z p
  let f1 : Coord → ℝ := fun p => heightPFirst g z 1 p * iteratedCoordPartial (ds ++ [1]) z p
  let fs : Coord → ℝ := fun p => ∑ c ∈ s, mixedFaaTerm g z (coordinateDirections ds) c p
  have hfirst (i : Fin 2) (p : Coord) (hp : p ∈ V) : |heightPFirst g z i p| ≤ C :=
    (heightPFirst_abs_le_fullP_one hg hU (hVU hp) (hyy p (hVU hp)) i).trans
      (hP 1 (by omega) p hp)
  have hm0 : AEStronglyMeasurable f0 (volume.restrict V) :=
    (((heightPFirst_contDiffOn hg hU hz hyy 0).continuousOn.mul
      (orderedPartial_contDiffOn hz hU (ds ++ [0])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hm1 : AEStronglyMeasurable f1 (volume.restrict V) :=
    (((heightPFirst_contDiffOn hg hU hz hyy 1).continuousOn.mul
      (orderedPartial_contDiffOn hz hU (ds ++ [1])).continuousOn).mono hVU).aestronglyMeasurable (μ := volume) hV
  have hb0 : eLpNorm f0 2 (volume.restrict V) ≤ ‖C‖ₑ * (H : ℝ≥0∞) :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
      (f := iteratedCoordPartial (ds ++ [0]) z) hV hC (hfirst 0) hm0).trans
      (mul_le_mul' le_rfl (hheight (ds ++ [0]) (by simp)))
  have hb1 : eLpNorm f1 2 (volume.restrict V) ≤ ‖C‖ₑ * (H : ℝ≥0∞) :=
    (scalar_coefficient_eLpNorm_two_of_aestronglyMeasurable
      (f := iteratedCoordPartial (ds ++ [1]) z) hV hC (hfirst 1) hm1).trans
      (mul_le_mul' le_rfl (hheight (ds ++ [1]) (by simp)))
  have hbs : eLpNorm fs 2 (volume.restrict V) ≤
      ∑ c : OrderedFinpartition ds.length, chainWordL2Budget C B H V ds.length ⟨c.length, c.partSize⟩ := by
    have hsum := finite_sum_eLpNorm_two s (fun c => mixedFaaTerm g z (coordinateDirections ds) c)
      (fun c => chainWordL2Budget C B H V ds.length ⟨c.length, c.partSize⟩)
      (fun c _ => ((mixedFaaTerm_continuousOn hg hU hz hyy (coordinateDirections ds) c).mono hVU).aestronglyMeasurable (μ := volume) hV)
      (fun c hc => mixedFaaTerm_eLpNorm_two hg hU hz hyy hV hVU ds hds hC hB hP hlow hheight c
        (Finset.mem_erase.mp hc).1)
    exact hsum.trans (Finset.sum_le_sum_of_subset (Finset.erase_subset _ _))
  have he : mixedFaaRemainder g z (by omega) (coordinateDirections ds) =ᵐ[volume.restrict V]
      (fun p => f0 p + f1 p + fs p) := by
    filter_upwards [ae_restrict_mem hV] with p hp
    exact mixedFaaRemainder_coordinate_eq hU hz (hVU hp) ds (by omega)
  rw [eLpNorm_congr_ae he]
  exact (eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by exact ((continuousOn_finsetSum s (fun c _ => mixedFaaTerm_continuousOn hg hU hz hyy (coordinateDirections ds) c)).mono hVU).aestronglyMeasurable hV) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    (add_le_add ((eLpNorm_add_le (hf := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (add_le_add hb0 hb1)) hbs)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Estimates_ActualRemainderRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry

theorem heightOriginalC0_contDiffOn {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (ell : ℕ) :
    ContDiffOn ℝ ∞ (heightOriginalC0 g z ell) U := by
  have hq := hessianQuotient_contDiffOn hg hU hz hyy
  exact (((coordinateDrift_contDiffOn hq hq hU).sub
    (hq.mul (heightPFirst_contDiffOn hg hU hz hyy 0))).sub
      (heightPFirst_contDiffOn hg hU hz hyy 1)).add
        (contDiffOn_const.mul (partial_contDiffOn (heightOriginalA_contDiffOn hg hU hz hyy) hU 1))

end SmoothLocal.Flow

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow

theorem actualHighRemainder_contDiffOn
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hz : ContDiffOn ℝ ∞ z U)
    (hD : ∀ p ∈ U, (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p)
    (hyy : ∀ p ∈ U, covHessian g z p 1 1 ≠ 0) (m : ℕ) :
    ContDiffOn ℝ ∞ (actualHighRemainder g z m) U := by
  have hh := driftOperator_contDiffOn hU (hessianQuotient_contDiffOn hg hU hz hyy)
    (heightOriginalA_contDiffOn hg hU hz hyy) (heightOriginalB_contDiffOn hg hU hz hyy (m+3))
    (heightOriginalC0_contDiffOn hg hU hz hyy (m+3)) (verticalJet_contDiffOn hU hz (m+3))
  exact hh.congr (fun p hp => (actual_differentiated_drift hg hU hz hD hyy m hp).symm)

end SmoothLocal.HighEquation

end

end OAI
end


