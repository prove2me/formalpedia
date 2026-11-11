-- Prove2me | Definitions.Def_Q226II000
-- name    : Q226II000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:34:21.090557+00:00
-- url     : https://prove2.me/theorems/e3877494-763d-4702-8e17-1ca2b3a92f8d
-- title:
--   Definitions bundle Q226II000 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 309 declarations of OpenAI's Lean: 149 definitions, 4 inductive types or structures and 156 theorems. The definitions and types are `OAI.SmoothLocal.Analytic.compactParameterIntegral`, `OAI.SmoothLocal.Analytic.compactParameterPartial`, `OAI.SmoothLocal.Flow.CapInductionFlow`, `OAI.SmoothLocal.Flow.CapInductionHeight`, `OAI.SmoothLocal.Flow.CapInterval`, `OAI.SmoothLocal.Flow.HeightDirectedBudgets`, `OAI.SmoothLocal.Flow.HeightNumericData`, `OAI.SmoothLocal.Flow.LowerCapRectangle`, `OAI.SmoothLocal.Flow.LowerCapRectangle.energyOuter`, `OAI.SmoothLocal.Flow.LowerCapRectangle.expand`, `OAI.SmoothLocal.Flow.LowerCapRectangle.image`, `OAI.SmoothLocal.Flow.LowerCapRectangle.margin`, `OAI.SmoothLocal.Flow.LowerCapRectangle.region`, `OAI.SmoothLocal.Flow.VerticalInterval`, `OAI.SmoothLocal.Flow.capChart`, `OAI.SmoothLocal.Flow.capChartDomain`, `OAI.SmoothLocal.Flow.capFlowHeight`, `OAI.SmoothLocal.Flow.flowAverageCoefficient`, `OAI.SmoothLocal.Flow.flowCoordinateBound`, `OAI.SmoothLocal.Flow.flowCoordinateMap`, `OAI.SmoothLocal.Flow.flowInteriorRadius`, `OAI.SmoothLocal.Flow.flowRhoJetBound`, `OAI.SmoothLocal.Flow.heightAJetBound`, `OAI.SmoothLocal.Flow.heightBJetBound`, `OAI.SmoothLocal.Flow.heightCapCValueBound`, `OAI.SmoothLocal.Flow.heightCapCoefficientBound`, `OAI.SmoothLocal.Flow.heightCapCurvatureBound`, `OAI.SmoothLocal.Flow.heightCapIntegralFactors`, `OAI.SmoothLocal.Flow.heightDirectedCoercivity`, `OAI.SmoothLocal.Flow.heightDirectedEpsilon`, `OAI.SmoothLocal.Flow.heightDirectedLambda`, `OAI.SmoothLocal.Flow.heightDirectedNumbers`, `OAI.SmoothLocal.Flow.heightDirectedSlope`, `OAI.SmoothLocal.Flow.heightG1JetBound`, `OAI.SmoothLocal.Flow.heightG1Lower`, `OAI.SmoothLocal.Flow.heightPhysicalCapConstant`, `OAI.SmoothLocal.Flow.heightRemainderBound`, `OAI.SmoothLocal.Flow.lowerCapConstant`, `OAI.SmoothLocal.Flow.modelOpenSquare`, `OAI.SmoothLocal.Flow.modelSquare` and 113 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Calculus_CoordinateDerivatives`, `IsometricImmersion_Calculus_CoordinateJetBounds`, `IsometricImmersion_Calculus_FinitePrimitive`, `IsometricImmersion_Calculus_HessianJetBounds`, `IsometricImmersion_Calculus_JointDerivative`, `IsometricImmersion_Calculus_MetricInverseJetBounds`, `IsometricImmersion_Calculus_QuotientLowBounds`, `IsometricImmersion_Calculus_SecondJetExtraction`, `IsometricImmersion_Calculus_SmoothCurry`, `IsometricImmersion_Calculus_VerticalSliceJets`, `IsometricImmersion_Caps_AllOrderPhysicalCap`, `IsometricImmersion_Caps_CapAreaFormula`, `IsometricImmersion_Caps_CapCutoffRectangle`, `IsometricImmersion_Caps_CapEllipticOverlap`, `IsometricImmersion_Caps_CapFlowJetBounds`, `IsometricImmersion_Caps_CapInductionData`, `IsometricImmersion_Caps_CapInteriorEnergy`, `IsometricImmersion_Caps_CapL2Basics`, `IsometricImmersion_Caps_CapOverlapCosts`, `IsometricImmersion_Caps_EllipticApplication`, `IsometricImmersion_Caps_EllipticCutoff`, `IsometricImmersion_Caps_EllipticRatio`, `IsometricImmersion_Caps_HeightCapLowData`, `IsometricImmersion_Caps_IntegratedCapOverlap`, `IsometricImmersion_Caps_NestedCapRectangles`, `IsometricImmersion_Caps_PhysicalCapTransport`, `IsometricImmersion_Comparison_ComparisonCoefficientDerivative`, `IsometricImmersion_Coordinates_AffinePullback`, `IsometricImmersion_Coordinates_CoordinateSwap`, `IsometricImmersion_Curvature_CurvatureFirstBounds`, `IsometricImmersion_Curvature_CurvatureParameter`, `IsometricImmersion_Darboux_ActualDriftCoefficients`, `IsometricImmersion_Darboux_ActualDriftEquation`, `IsometricImmersion_Darboux_DarbouxJet`, `IsometricImmersion_Darboux_Drift`, `IsometricImmersion_Darboux_DriftTransportAlgebra`, `IsometricImmersion_Darboux_HeightPrincipalBounds`, `IsometricImmersion_Darboux_ModelPrincipal`, `IsometricImmersion_Darboux_SixVariableDarboux`, `IsometricImmersion_Darboux_SixVariableQ`, `IsometricImmersion_Energy_DirectedDefectCost`, `IsometricImmersion_Energy_DirectedFarNegative`, `IsometricImmersion_Energy_DirectedFluxCost`, `IsometricImmersion_Energy_DirectedParameterChoice`, `IsometricImmersion_Energy_DirectedWeightJetCost`, `IsometricImmersion_Energy_FiniteProductL2`, `IsometricImmersion_Energy_FiniteSumL2`, `IsometricImmersion_Energy_HeightEnergy`, `IsometricImmersion_Energy_HeightEnergyJetBounds`, `IsometricImmersion_Energy_MultiplierIntegral`, `IsometricImmersion_Energy_RectangleSobolev`, `IsometricImmersion_Energy_RectangleSobolevOne`, `IsometricImmersion_Energy_RegionSobolev`, `IsometricImmersion_Energy_WeightPrimitive`, `IsometricImmersion_Estimates_ActualHighEquation`, `IsometricImmersion_Flows_CompactParameterIntegral`, `IsometricImmersion_Flows_ConstructedHeightFlow`, `IsometricImmersion_Flows_FlowBounds`, `IsometricImmersion_Flows_FlowCurvature`, `IsometricImmersion_Flows_FlowExistence`, `IsometricImmersion_Flows_FlowImageFirstBounds`, `IsometricImmersion_Flows_FlowImageMargin`, `IsometricImmersion_Flows_FlowJointSmooth`, `IsometricImmersion_Flows_FlowLowBounds`, `IsometricImmersion_Flows_FlowParameter`, `IsometricImmersion_Flows_FlowParameterContinuity`, `IsometricImmersion_Flows_FlowSecondVariation`, `IsometricImmersion_Flows_FlowSobolev`, `IsometricImmersion_Flows_FlowTimeVariation`, `IsometricImmersion_Flows_FlowVariation`, `IsometricImmersion_Flows_HeightFlowUniformBounds`, `IsometricImmersion_Immersions_HeightCoefficientClosedBounds`, `IsometricImmersion_Immersions_HeightNumericParameters`, `IsometricImmersion_Immersions_HeightPFirstBounds`, `IsometricImmersion_Metric`, `IsometricImmersion_Metrics_MetricLocality`, `IsometricImmersion_Metrics_ModelCoercivity`, `IsometricImmersion_Metrics_WarpedMetric`, `IsometricImmersion_Taylor_ChainResidual`, `IsometricImmersion_Taylor_ChainTermDerivative`, `IsometricImmersion_Volterra_VolterraDifferentiation`, `IsometricImmersion_Volterra_VolterraJointSmooth`, `IsometricImmersion_Volterra_VolterraOperator`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`.
--
--   **Imported by** (directly, in this split): the bundles `Q226II003`, `Q226II004`, `Q226II005` and `Q226II006`.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 334; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
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
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Interval
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_IsometricImmersion

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_CoordinateDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators
open Filter

namespace SmoothLocal.Geometry

def coordPartial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : Fin 2) (f : Coord → V) (p : Coord) : V :=
  fderiv ℝ f p (Pi.single i 1)

section Height
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {F : Coord → V} {p : Coord} {U : Set Coord}

theorem partial_contDiffOn (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (coordPartial i F) U := by
  exact (hF.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const

end Height
end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix ContDiff
namespace SmoothLocal.Geometry

abbrev MetricField := Coord → Matrix (Fin 2) (Fin 2) ℝ

def inverseMetric (g : MetricField) (p : Coord) := (g p)⁻¹

def christoffel (g : MetricField) (k i j : Fin 2) (p : Coord) : ℝ :=
  (1 / 2 : ℝ) * ∑ l, inverseMetric g p k l *
    (coordPartial i (fun q => g q j l) p + coordPartial j (fun q => g q i l) p -
      coordPartial l (fun q => g q i j) p)

def covHessian (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  coordPartial i (coordPartial j z) p - ∑ k, christoffel g k i j p * coordPartial k z p

def covectorNormSq (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  ∑ i, ∑ j, inverseMetric g p i j * coordPartial i z p * coordPartial j z p

def riemann (g : MetricField) (l k i j : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (christoffel g l j k) p - coordPartial j (christoffel g l i k) p +
    ∑ m, (christoffel g m j k p * christoffel g l i m p -
      christoffel g m i k p * christoffel g l j m p)

def gaussianCurvature (g : MetricField) (p : Coord) : ℝ :=
  (∑ l, g p 0 l * riemann g l 1 0 1 p) / (g p).det

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_HeightEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

def heightEnergy (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  (g p).det * (1 - covectorNormSq g z p)

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

def iteratedCoordPartial {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Fin 2) → (Coord → V) → Coord → V
  | [], f => f
  | i :: is, f => coordPartial i (iteratedCoordPartial is f)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_QuotientLowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry.LowQuotient

def bound0 (M c : ℝ) : ℝ := M / c
def bound1 (M c : ℝ) : ℝ := (M + M * bound0 M c) / c
def bound2 (M c : ℝ) : ℝ := (M + M * bound0 M c + 2 * M * bound1 M c) / c
def bound3 (M c : ℝ) : ℝ :=
  (M + M * bound0 M c + 3 * M * bound1 M c + 3 * M * bound2 M c) / c
def boundThroughThree (M c : ℝ) : ℝ := bound0 M c + bound1 M c + bound2 M c + bound3 M c

theorem bounds_nonneg {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c) :
    0 ≤ bound0 M c ∧ 0 ≤ bound1 M c ∧ 0 ≤ bound2 M c ∧ 0 ≤ bound3 M c := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> dsimp [bound0, bound1, bound2, bound3] <;> positivity

end SmoothLocal.Geometry.LowQuotient

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_CoordinateJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def CoordinateBound (f : Coord → ℝ) (U : Set Coord) (n : ℕ) (M : ℝ) : Prop :=
  ∀ ds : List (Fin 2), ds.length ≤ n → ∀ p ∈ U, |iteratedCoordPartial ds f p| ≤ M

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_JointDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

def jointDifferential (fx fy : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight fx +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight fy

theorem jointDifferential_eq_coprod (fx fy : ℝ) :
    jointDifferential fx fy =
      (ContinuousLinearMap.toSpanSingleton ℝ fx).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ fy) := by
  apply ContinuousLinearMap.ext
  intro v
  simp [jointDifferential]

theorem hasFDerivAt_of_continuous_partials
    {s : Set (ℝ × ℝ)} (hs : IsOpen s) {f fx fy : (ℝ × ℝ) → ℝ}
    (hcx : ContinuousOn fx s) (hcy : ContinuousOn fy s)
    (hdx : ∀ p ∈ s, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hdy : ∀ p ∈ s, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2)
    {p : ℝ × ℝ} (hp : p ∈ s) :
    HasFDerivAt f (jointDifferential (fx p) (fy p)) p := by
  have hspan : Continuous (ContinuousLinearMap.toSpanSingleton ℝ :
      ℝ → (ℝ →L[ℝ] ℝ)) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous
  have hfirst : ∀ᶠ q in 𝓝 p,
      HasFDerivAt (fun x => f (x, q.2))
        (ContinuousLinearMap.toSpanSingleton ℝ (fx q)) q.1 := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact (hdx q hq).hasFDerivAt
  have hsecond : ∀ᶠ q in 𝓝 p,
      HasFDerivAt (fun y => f (q.1, y))
        (ContinuousLinearMap.toSpanSingleton ℝ (fy q)) q.2 := by
    filter_upwards [hs.mem_nhds hp] with q hq
    exact (hdy q hq).hasFDerivAt
  have hfull := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ)
    (f := fun x y => f (x, y))
    (f₁ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (fx (x, y)))
    (f₂ := fun x y => ContinuousLinearMap.toSpanSingleton ℝ (fy (x, y)))
    hfirst hsecond
    (hspan.continuousAt.comp (hcx.continuousAt (hs.mem_nhds hp)))
    (hspan.continuousAt.comp (hcy.continuousAt (hs.mem_nhds hp)))
  rw [jointDifferential_eq_coprod]
  exact hfull.hasFDerivAt

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_SmoothCurry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology Interval ContDiff

namespace SmoothLocal.ODE

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_continuousMap_of_eval
    {a b : ℝ} {F P : ℝ → C(X, E)}
    (hP : ContinuousOn P (Ioo a b))
    (hpoint : ∀ t ∈ Ioo a b, ∀ x : X,
      HasDerivAt (fun s => F s x) (P t x) t)
    {t : ℝ} (ht : t ∈ Ioo a b) : HasDerivAt F (P t) t := by
  have hmeas : StronglyMeasurableAtFilter P (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hP t ht
  have hprim : HasDerivAt (fun y => F t + ∫ s in t..y, P s) (P t) t :=
    (intervalIntegral.integral_hasDerivAt_right
      (IntervalIntegrable.refl : IntervalIntegrable P volume t t)
      hmeas (hP.continuousAt (Ioo_mem_nhds ht.1 ht.2))).const_add (F t)
  have heq : F =ᶠ[𝓝 t] (fun y => F t + ∫ s in t..y, P s) := by
    apply Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2)
    intro y hy
    have hseg : uIcc t y ⊆ Ioo a b := by
      intro s hs
      exact ⟨lt_of_lt_of_le (lt_min ht.1 hy.1) hs.1,
        lt_of_le_of_lt hs.2 (max_lt ht.2 hy.2)⟩
    have hPI : IntervalIntegrable P volume t y := (hP.mono hseg).intervalIntegrable
    apply ContinuousMap.ext
    intro x
    have hPIx : IntervalIntegrable (fun s => P s x) volume t y :=
      ((ContinuousMap.evalCLM ℝ x).continuous.comp_continuousOn
        (hP.mono hseg)).intervalIntegrable
    have hscalar : (∫ s in t..y, P s x) = F y x - F t x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => hpoint s (hseg hs) x) hPIx
    change F y x = F t x + (ContinuousMap.evalCLM ℝ x) (∫ s in t..y, P s)
    rw [← (ContinuousMap.evalCLM ℝ x).intervalIntegral_comp_comm hPI]
    change F y x = F t x + ∫ s in t..y, P s x
    rw [hscalar]
    abel
  exact hprim.congr_of_eventuallyEq heq

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.ODE

abbrev IntervalFunctions (r : ℝ) := C(Icc (-r) r, ℝ)

def intervalExtension (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) : C(ℝ, ℝ) :=
  letI : Fact (-r ≤ r) := ⟨by linarith⟩
  ContinuousMap.IccExtendCM h

theorem intervalExtension_apply_of_mem (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) {x : ℝ} (hx : x ∈ Icc (-r) r) :
    intervalExtension r hr h x = h ⟨x, hx⟩ := by
  let : Fact (-r ≤ r) := ⟨by linarith⟩
  exact ContinuousMap.IccExtendCM_of_mem hx

theorem intervalExtension_norm_le (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : ℝ) :
    ‖intervalExtension r hr h x‖ ≤ ‖h‖ := by
  exact h.norm_coe_le_norm _

@[simp]
theorem intervalExtension_add (r : ℝ) (hr : 0 < r)
    (h k : IntervalFunctions r) (x : ℝ) :
    intervalExtension r hr (h + k) x =
      intervalExtension r hr h x + intervalExtension r hr k x := rfl

@[simp]
theorem intervalExtension_smul (r : ℝ) (hr : 0 < r)
    (c : ℝ) (h : IntervalFunctions r) (x : ℝ) :
    intervalExtension r hr (c • h) x = c • intervalExtension r hr h x := rfl

def primitiveFunction (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) (x : ℝ) : ℝ :=
  ∫ t in 0..x, intervalExtension r hr h t

theorem primitiveFunction_continuous (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) : Continuous (primitiveFunction r hr h) :=
  (intervalIntegral.differentiable_integral_of_continuous
    (intervalExtension r hr h).continuous).continuous

theorem primitiveFunction_hasDerivAt (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : ℝ) :
    HasDerivAt (primitiveFunction r hr h) (intervalExtension r hr h x) x :=
  intervalIntegral.integral_hasDerivAt_right
    ((intervalExtension r hr h).continuous.intervalIntegrable 0 x)
    ((intervalExtension r hr h).continuous.stronglyMeasurableAtFilter volume (𝓝 x))
    (intervalExtension r hr h).continuous.continuousAt

def primitiveMap (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) : IntervalFunctions r :=
  ⟨fun x => primitiveFunction r hr h x,
    (primitiveFunction_continuous r hr h).comp continuous_subtype_val⟩

@[simp]
theorem primitiveMap_apply (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : Icc (-r) r) :
    primitiveMap r hr h x = ∫ t in 0..(x : ℝ), intervalExtension r hr h t := rfl

def primitiveLinearMap (r : ℝ) (hr : 0 < r) :
    IntervalFunctions r →ₗ[ℝ] IntervalFunctions r where
  toFun := primitiveMap r hr
  map_add' h k := by
    apply ContinuousMap.ext
    intro x
    change (∫ t in 0..(x : ℝ), intervalExtension r hr (h + k) t) =
      (∫ t in 0..(x : ℝ), intervalExtension r hr h t) +
      (∫ t in 0..(x : ℝ), intervalExtension r hr k t)
    simp only [intervalExtension_add]
    exact intervalIntegral.integral_add
      ((intervalExtension r hr h).continuous.intervalIntegrable 0 x)
      ((intervalExtension r hr k).continuous.intervalIntegrable 0 x)
  map_smul' c h := by
    apply ContinuousMap.ext
    intro x
    change (∫ t in 0..(x : ℝ), intervalExtension r hr (c • h) t) =
      c • (∫ t in 0..(x : ℝ), intervalExtension r hr h t)
    simp only [intervalExtension_smul]
    exact intervalIntegral.integral_smul c (fun t => intervalExtension r hr h t)

theorem primitiveMap_norm_le (r : ℝ) (hr : 0 < r) (h : IntervalFunctions r) :
    ‖primitiveMap r hr h‖ ≤ r * ‖h‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg hr.le (norm_nonneg h))).mpr
  intro x
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := (x : ℝ)) (C := ‖h‖)
    (f := fun t => intervalExtension r hr h t)
    (fun t _ => intervalExtension_norm_le r hr h t)
  have hx : |(x : ℝ)| ≤ r := abs_le.mpr x.2
  change ‖∫ t in 0..(x : ℝ), intervalExtension r hr h t‖ ≤ r * ‖h‖
  calc
    ‖∫ t in 0..(x : ℝ), intervalExtension r hr h t‖ ≤ ‖h‖ * |(x : ℝ)| := by
      simpa only [sub_zero] using hi
    _ ≤ ‖h‖ * r := mul_le_mul_of_nonneg_left hx (norm_nonneg h)
    _ = r * ‖h‖ := mul_comm _ _

def primitiveCLM (r : ℝ) (hr : 0 < r) :
    IntervalFunctions r →L[ℝ] IntervalFunctions r :=
  (primitiveLinearMap r hr).mkContinuous r (primitiveMap_norm_le r hr)

@[simp]
theorem primitiveCLM_apply (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) (x : Icc (-r) r) :
    primitiveCLM r hr h x = ∫ t in 0..(x : ℝ), intervalExtension r hr h t := rfl

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology

namespace SmoothLocal.ODE
open SmoothLocal.Geometry

def coordinatePoint (x y : ℝ) : Coord :=
  x • Pi.single 0 1 + y • Pi.single 1 1

theorem coordinatePoint_hasDerivAt_y (x y : ℝ) :
    HasDerivAt (coordinatePoint x) (Pi.single 1 (1 : ℝ) : Coord) y := by
  change HasDerivAt (fun t : ℝ => x • (Pi.single 0 (1 : ℝ) : Coord) +
    t • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) y
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id y).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (x • (Pi.single 0 (1 : ℝ) : Coord))

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraDifferentiation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

def intervalExtensionEvalCLM (r : ℝ) (hr : 0 < r) (x : ℝ) :
    IntervalFunctions r →L[ℝ] ℝ :=
  letI : Fact (-r ≤ r) := ⟨by linarith⟩
  ContinuousMap.evalCLM ℝ (ContinuousMap.projIccCM (a := -r) (b := r) x)

theorem intervalExtension_family_continuousOn (r : ℝ) (hr : 0 < r)
    {s : Set ℝ} {F : ℝ → IntervalFunctions r} (hF : ContinuousOn F s) :
    ContinuousOn (fun p : ℝ × ℝ => intervalExtension r hr (F p.2) p.1)
      (univ ×ˢ s) := by
  let : Fact (-r ≤ r) := ⟨by linarith⟩
  have hext : ContinuousOn (fun y => intervalExtension r hr (F y)) s :=
    ContinuousMap.IccExtendCM.continuous.comp_continuousOn hF
  exact (hext.comp continuous_snd.continuousOn (fun _ hp => hp.2)).eval
    continuous_fst.continuousOn

theorem intervalExtension_family_hasDerivAt (r : ℝ) (hr : 0 < r)
    {F : ℝ → IntervalFunctions r} {F' : IntervalFunctions r} {y : ℝ}
    (hF : HasDerivAt F F' y) (x : ℝ) :
    HasDerivAt (fun t => intervalExtension r hr (F t) x)
      (intervalExtension r hr F' x) y := by
  exact (intervalExtensionEvalCLM r hr x).hasFDerivAt.comp_hasDerivAt y hF

theorem intervalExtension_primitive_hasDerivAt (r : ℝ) (hr : 0 < r)
    (h : IntervalFunctions r) {x : ℝ} (hx : x ∈ Ioo (-r) r) :
    HasDerivAt (fun t => intervalExtension r hr (primitiveCLM r hr h) t)
      (intervalExtension r hr h x) x := by
  apply (primitiveFunction_hasDerivAt r hr h x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
  rw [intervalExtension_apply_of_mem r hr _ ⟨ht.1.le, ht.2.le⟩]
  rfl

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Volterra_VolterraJointSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.ODE

theorem contDiffOn_succ_of_continuous_partials
    {s : Set (ℝ × ℝ)} (hs : IsOpen s) {f fx fy : (ℝ × ℝ) → ℝ} (n : ℕ)
    (hfx : ContDiffOn ℝ n fx s) (hfy : ContDiffOn ℝ n fy s)
    (hdx : ∀ p ∈ s, HasDerivAt (fun x => f (x, p.2)) (fx p) p.1)
    (hdy : ∀ p ∈ s, HasDerivAt (fun y => f (p.1, y)) (fy p) p.2) :
    ContDiffOn ℝ (n + 1 : ℕ) f s := by
  have hd (p : ℝ × ℝ) (hp : p ∈ s) :
      HasFDerivAt f (jointDifferential (fx p) (fy p)) p :=
    hasFDerivAt_of_continuous_partials hs hfx.continuousOn hfy.continuousOn hdx hdy hp
  have hnext : ContDiffOn ℝ ((n : ℕ∞ω) + 1) f s := by
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    have hfield : ContDiffOn ℝ n (fun p => jointDifferential (fx p) (fy p)) s :=
      (contDiffOn_const.smulRight hfx).add (contDiffOn_const.smulRight hfy)
    exact hfield.congr (fun p hp => (hd p hp).fderiv)
  simpa only [Nat.cast_add, Nat.cast_one] using hnext

end SmoothLocal.ODE

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_WeightPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry SmoothLocal.ODE

def coordinateRectangle (R a b : ℝ) : Set Coord :=
  {p | p 0 ∈ Ioo (-R) R ∧ p 1 ∈ Ioo a b}

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_FinitePrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.ODE

def pairRectangle (R a b : ℝ) : Set (ℝ × ℝ) := Ioo (-R) R ×ˢ Ioo a b

def pairPrimitive (B : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ t in 0..p.1, B (t, p.2)

def pairPartialY (B : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ B p (0, 1)

def pairCompactFamily (B : ℝ × ℝ → ℝ) (r : ℝ) (y : ℝ) : IntervalFunctions r :=
  ContinuousMap.mkD (fun x : Icc (-r) r => B (x, y)) 0

theorem pairRectangle_isOpen (R a b : ℝ) : IsOpen (pairRectangle R a b) :=
  isOpen_Ioo.prod isOpen_Ioo

theorem exists_compact_time_interval {R x : ℝ} (hx : x ∈ Ioo (-R) R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ x ∈ Ioo (-r) r := by
  have hxa : |x| < R := abs_lt.mpr hx
  refine ⟨(|x| + R) / 2, ?_, ?_, ?_⟩
  · nlinarith [abs_nonneg x]
  · linarith
  · apply abs_lt.mp
    linarith

theorem pairCompactFamily_joint_continuous {B : ℝ × ℝ → ℝ} {R a b r : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hrR : r < R) :
    ContinuousOn (fun p : ℝ × Icc (-r) r => B (p.2, p.1))
      (Ioo a b ×ˢ (univ : Set (Icc (-r) r))) := by
  exact hB.comp (by fun_prop)
    (fun p hp => ⟨⟨(neg_lt_neg hrR).trans_le p.2.2.1,
      p.2.2.2.trans_lt hrR⟩, hp.1⟩)

theorem pairCompactFamily_continuousOn {B : ℝ × ℝ → ℝ} {R a b r : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hrR : r < R) :
    ContinuousOn (pairCompactFamily B r) (Ioo a b) :=
  ContinuousMap.continuousOn_mkD_of_uncurry _ 0 (pairCompactFamily_joint_continuous hB hrR)

theorem pairCompactFamily_apply {B : ℝ × ℝ → ℝ} {R a b r y : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hrR : r < R)
    (hy : y ∈ Ioo a b) (x : Icc (-r) r) : pairCompactFamily B r y x = B (x, y) := by
  have hc : Continuous (fun t : Icc (-r) r => B (t, y)) :=
    (pairCompactFamily_joint_continuous hB hrR).comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨hy, mem_univ _⟩)
  unfold pairCompactFamily
  rw [ContinuousMap.mkD_of_continuous hc]
  rfl

theorem pairPrimitive_eq_clamped {B : ℝ × ℝ → ℝ} {R a b r x y : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) (hr : 0 < r) (hrR : r < R)
    (hx : x ∈ Ioo (-r) r) (hy : y ∈ Ioo a b) :
    pairPrimitive B (x, y) =
      intervalExtension r hr (primitiveCLM r hr (pairCompactFamily B r y)) x := by
  rw [intervalExtension_apply_of_mem r hr _ ⟨hx.1.le, hx.2.le⟩, primitiveCLM_apply]
  unfold pairPrimitive
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (-r) r :=
    uIcc_subset_Icc ⟨by linarith, hr.le⟩ ⟨hx.1.le, hx.2.le⟩ ht
  rw [intervalExtension_apply_of_mem r hr _ ht', pairCompactFamily_apply hB hrR hy]

theorem pairPrimitive_continuousOn {B : ℝ × ℝ → ℝ} {R a b : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b)) :
    ContinuousOn (pairPrimitive B) (pairRectangle R a b) := by
  intro p hp
  obtain ⟨r, hr, hrR, hpr⟩ := exists_compact_time_interval hp.1
  have hF := (primitiveCLM r hr).continuous.comp_continuousOn
    (pairCompactFamily_continuousOn hB hrR)
  have hc := intervalExtension_family_continuousOn r hr hF
  have hn : (univ : Set ℝ) ×ˢ Ioo a b ∈ 𝓝 p :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hp.2⟩
  have he : pairPrimitive B =ᶠ[𝓝 p]
      (fun q => intervalExtension r hr (primitiveCLM r hr (pairCompactFamily B r q.2)) q.1) := by
    filter_upwards [(pairRectangle_isOpen r a b).mem_nhds ⟨hpr, hp.2⟩] with q hq
    exact pairPrimitive_eq_clamped hB hr hrR hq.1 hq.2
  exact ((hc.continuousAt hn).congr_of_eventuallyEq he).continuousWithinAt

theorem pairPartialY_contDiffOn {B : ℝ × ℝ → ℝ} {R a b : ℝ} (n : ℕ)
    (hB : ContDiffOn ℝ (n + 1 : ℕ) B (pairRectangle R a b)) :
    ContDiffOn ℝ n (pairPartialY B) (pairRectangle R a b) := by
  have hd : ContDiffOn ℝ n (fderiv ℝ B) (pairRectangle R a b) :=
    hB.fderiv_of_isOpen (pairRectangle_isOpen R a b) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hd.clm_apply contDiffOn_const

theorem pairCompactFamily_hasDerivAt {B : ℝ × ℝ → ℝ} {R a b r y : ℝ}
    (hB : ContDiffOn ℝ 1 B (pairRectangle R a b)) (hrR : r < R) (hy : y ∈ Ioo a b) :
    HasDerivAt (pairCompactFamily B r) (pairCompactFamily (pairPartialY B) r y) y := by
  have hP : ContinuousOn (pairPartialY B) (pairRectangle R a b) :=
    (pairPartialY_contDiffOn 0 hB).continuousOn
  apply hasDerivAt_continuousMap_of_eval (pairCompactFamily_continuousOn hP hrR) _ hy
  intro u hu x
  have hx : (x : ℝ) ∈ Ioo (-R) R :=
    ⟨(neg_lt_neg hrR).trans_le x.2.1, x.2.2.trans_lt hrR⟩
  have hxu : ((x : ℝ), u) ∈ pairRectangle R a b := ⟨hx, hu⟩
  have hd := ((hB.contDiffAt ((pairRectangle_isOpen R a b).mem_nhds hxu)).differentiableAt
    (by norm_num)).hasFDerivAt
  have hs : HasDerivAt (fun v : ℝ => ((x : ℝ), v)) (0, 1) u :=
    (hasDerivAt_const u (x : ℝ)).prodMk (hasDerivAt_id u)
  have hpoint : HasDerivAt (fun v => B (x, v)) (pairPartialY B (x, u)) u :=
    hd.comp_hasDerivAt u hs
  rw [pairCompactFamily_apply hP hrR hu x]
  apply hpoint.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hu] with v hv
  exact pairCompactFamily_apply hB.continuousOn hrR hv x

theorem pairPrimitive_hasDerivAt_y {B : ℝ × ℝ → ℝ} {R a b x y : ℝ}
    (hB : ContDiffOn ℝ 1 B (pairRectangle R a b))
    (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    HasDerivAt (fun v => pairPrimitive B (x, v)) (pairPrimitive (pairPartialY B) (x, y)) y := by
  obtain ⟨r, hr, hrR, hxr⟩ := exists_compact_time_interval hx
  have hP : ContinuousOn (pairPartialY B) (pairRectangle R a b) :=
    (pairPartialY_contDiffOn 0 hB).continuousOn
  have hFB := pairCompactFamily_hasDerivAt hB hrR hy
  have hPB := (primitiveCLM r hr).hasFDerivAt.comp_hasDerivAt y hFB
  have hd := intervalExtension_family_hasDerivAt r hr hPB x
  rw [← pairPrimitive_eq_clamped hP hr hrR hxr hy] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hy] with v hv
  exact pairPrimitive_eq_clamped hB.continuousOn hr hrR hxr hv

theorem pairPrimitive_hasDerivAt_x {B : ℝ × ℝ → ℝ} {R a b x y : ℝ}
    (hB : ContinuousOn B (pairRectangle R a b))
    (hx : x ∈ Ioo (-R) R) (hy : y ∈ Ioo a b) :
    HasDerivAt (fun t => pairPrimitive B (t, y)) (B (x, y)) x := by
  obtain ⟨r, hr, hrR, hxr⟩ := exists_compact_time_interval hx
  have hd := intervalExtension_primitive_hasDerivAt r hr (pairCompactFamily B r y) hxr
  rw [intervalExtension_apply_of_mem r hr _ ⟨hxr.1.le, hxr.2.le⟩,
    pairCompactFamily_apply hB hrR hy] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hxr] with t ht
  exact pairPrimitive_eq_clamped hB hr hrR ht hy

theorem pairPrimitive_contDiffOn_nat (n : ℕ) {B : ℝ × ℝ → ℝ} {R a b : ℝ}
    (hB : ContDiffOn ℝ n B (pairRectangle R a b)) :
    ContDiffOn ℝ n (pairPrimitive B) (pairRectangle R a b) := by
  induction n generalizing B with
  | zero =>
      simpa only [Nat.cast_zero, contDiffOn_zero] using pairPrimitive_continuousOn hB.continuousOn
  | succ n hn =>
      have hB1 : ContDiffOn ℝ 1 B (pairRectangle R a b) := hB.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
      apply contDiffOn_succ_of_continuous_partials (pairRectangle_isOpen R a b) n
        (hB.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hn (pairPartialY_contDiffOn n hB))
      · intro p hp
        exact pairPrimitive_hasDerivAt_x hB.continuousOn hp.1 hp.2
      · intro p hp
        exact pairPrimitive_hasDerivAt_y hB1 hp.1 hp.2

end SmoothLocal.Flow

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

def hessianQuotient (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  covHessian g z p 0 1 / covHessian g z p 1 1

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MetricInverseJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Geometry

def metricQuotientNumeratorBound (G : ℝ) : ℝ := G + 16 * G^2
def metricInverseJetBound (G d : ℝ) : ℝ :=
  LowQuotient.boundThroughThree (metricQuotientNumeratorBound G) d

theorem metricInverseJetBound_nonneg {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d) :
    0 ≤ metricInverseJetBound G d := by
  have hN : 0 ≤ metricQuotientNumeratorBound G := by dsimp [metricQuotientNumeratorBound] <;> positivity
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg hN hd
  dsimp [metricInverseJetBound, LowQuotient.boundThroughThree]
  positivity

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

def christoffelJetBound (G d : ℝ) : ℝ := 24 * metricInverseJetBound G d * G
def hessianJetBound (G Z d : ℝ) : ℝ := Z + 16 * christoffelJetBound G d * Z

theorem christoffelJetBound_nonneg {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d) :
    0 ≤ christoffelJetBound G d := by
  have hI := metricInverseJetBound_nonneg hG hd
  dsimp [christoffelJetBound]
  positivity

theorem hessianJetBound_nonneg {G Z d : ℝ} (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) :
    0 ≤ hessianJetBound G Z d := by
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [hessianJetBound]
  positivity

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_DarbouxJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def jetConnection (g : MetricField) (p : Coord) (a b : Fin 2) (u : Coord) : ℝ :=
  ∑ r, christoffel g r a b p * u r

def jetMixed (g : MetricField) (p : Coord) (b : ℝ) (u : Coord) : ℝ :=
  b - jetConnection g p 0 1 u

def jetYY (g : MetricField) (p : Coord) (c : ℝ) (u : Coord) : ℝ :=
  c - jetConnection g p 1 1 u

def jetEnergy (g : MetricField) (p : Coord) (u : Coord) : ℝ :=
  (g p).det - (g p 1 1 * (u 0) ^ 2 -
    (g p 0 1 + g p 1 0) * u 0 * u 1 + g p 0 0 * (u 1) ^ 2)

def jetNumerator (g : MetricField) (p : Coord) (b : ℝ) (u : Coord) : ℝ :=
  (jetMixed g p b u) ^ 2 + gaussianCurvature g p * jetEnergy g p u

def solvedDarboux (g : MetricField) (p : Coord) (b c : ℝ) (u : Coord) : ℝ :=
  jetConnection g p 0 0 u + jetNumerator g p b u / jetYY g p c u

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

abbrev DarbouxState := Fin 6 → ℝ

def statePoint (w : DarbouxState) : Coord := ![w 0, w 1]
def stateGradient (w : DarbouxState) : Coord := ![w 2, w 3]

def sixVariableP (g : MetricField) (w : DarbouxState) : ℝ :=
  solvedDarboux g (statePoint w) (w 4) (w 5) (stateGradient w)

variable {g : MetricField} {U : Set Coord}

def solutionJet (z : Coord → ℝ) (p : Coord) : DarbouxState :=
  ![p 0, p 1, coordPartial 0 z p, coordPartial 1 z p,
    coordPartial 0 (coordPartial 1 z) p, coordPartial 1 (coordPartial 1 z) p]

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_VerticalSliceJets
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

def verticalJet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Coord → V) : ℕ → Coord → V
  | 0 => f
  | n + 1 => coordPartial 1 (verticalJet f n)

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_Drift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SmoothLocal.DriftAlgebra

theorem explicit_drift_remainder
    (h E hy q cxy cyy dyy J ex ey Ey : ℝ)
    (hne : h ≠ 0)
    (energy_y : Ey = 2 * (cxy + dyy) * E - 2 * h * J)
    (energy_jet : q * ex + ey = -2 * J) :
    (Ey / h ^ 2 - E * hy / h ^ 3 - E * (cxy - q * cyy) / h ^ 2 + J / h) -
        q * (ex / h + E * cyy / h ^ 2) - (ey / h + E * dyy / h ^ 2) =
      E / h ^ 2 * (cxy + dyy - hy / h) + J / h := by
  have hey : ey = -2 * J - q * ex := by linarith [energy_jet]
  rw [energy_y, hey]
  field_simp [hne]
  ring

theorem transverse_coefficient_polynomial
    (ell K Ky G Gy rho sigma R : ℝ) :
    K * G * sigma + rho * (Ky * G + K * R + ell * (Ky * G + K * Gy)) =
      (ell + 1) * (G * rho * Ky + K * (rho * Gy + 2 * G * sigma)) +
        K * (rho * R - rho * Gy - (2 * ell + 1) * G * sigma) := by
  ring

theorem transverse_coefficient_factor
    (ell K G Gy rho sigma R : ℝ) (hG : G ≠ 0) (hrho : rho ≠ 0) :
    K * (rho * R - rho * Gy - (2 * ell + 1) * G * sigma) =
      (K * G * rho ^ 2) *
        ((R - Gy) / (G * rho) - (2 * ell + 1) * sigma / rho ^ 2) := by
  field_simp [hG, hrho]

end SmoothLocal.DriftAlgebra

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_DriftTransportAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SmoothLocal.DriftAlgebra

theorem quotient_transport_algebra
    (A B h Ay Bx By hx hy K Ky E Ey a b c d e f J0 J1 : ℝ)
    (hne : h ≠ 0)
    (hdet : A * h - B ^ 2 = K * E)
    (hdety : Ay * h + A * hy - 2 * B * By = Ky * E + K * Ey)
    (hBx : Bx - Ay = -b * A + (a - e) * B + d * h + K * J0)
    (hhx : hx - By = -c * A + (b - f) * B + e * h + K * J1) :
    (Bx - (B / h) * By) / h - (B / h) * (hx - (B / h) * hy) / h -
      (B / h) * (a - 2 * (B / h) * b + (B / h) ^ 2 * c) -
      (d - 2 * (B / h) * e + (B / h) ^ 2 * f) =
        Ky * (E / h ^ 2) + K *
          (Ey / h ^ 2 - E * hy / h ^ 3 -
            (E / h ^ 2) * (b - (B / h) * c) + (J0 - (B / h) * J1) / h) := by
  have hA : A = (B ^ 2 + K * E) / h :=
    (eq_div_iff hne).2 (by linarith [hdet])
  have hAy : Ay = (Ky * E + K * Ey - A * hy + 2 * B * By) / h :=
    (eq_div_iff hne).2 (by linarith [hdety])
  have hBx' : Bx = Ay - b * A + (a - e) * B + d * h + K * J0 := by
    linarith [hBx]
  have hhx' : hx = By - c * A + (b - f) * B + e * h + K * J1 := by
    linarith [hhx]
  rw [hBx', hhx', hAy, hA]
  field_simp [hne]
  ring

end SmoothLocal.DriftAlgebra

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_ActualDriftEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Matrix BigOperators

namespace SmoothLocal.Geometry

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

def heightPFirst (g : MetricField) (z : Coord → ℝ) (i : Fin 2) (p : Coord) : ℝ :=
  coordPartial i (solvedDarboux g p
    (coordPartial 0 (coordPartial 1 z) p) (coordPartial 1 (coordPartial 1 z) p))
    (fun r => coordPartial r z p)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ModelCoercivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model

open SmoothLocal.Geometry SmoothLocal.Weighted

def modelCoercivityMargin (g0 kappa rhoMax epsilon : ℝ) (ell : ℕ) : ℝ :=
  g0 * kappa * min (3 * ((ell : ℝ) + 1 / 2) / (4 * rhoMax)) (5 * epsilon / 16)

theorem modelCoercivityMargin_pos {g0 kappa rhoMax epsilon : ℝ} (ell : ℕ)
    (hg0 : 0 < g0) (hkappa : 0 < kappa) (hrho : 0 < rhoMax) (heps : 0 < epsilon) :
    0 < modelCoercivityMargin g0 kappa rhoMax epsilon ell := by
  have hell : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  unfold modelCoercivityMargin
  positivity

end SmoothLocal.Model

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_ModelPrincipal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Model
open SmoothLocal.Geometry SmoothLocal.Weighted

def modelPrincipalRemainderBound (ell : ℕ) (R MG : ℝ) : ℝ :=
  ((ell : ℝ) + 1 / 2 + R / 2) * MG

def modelPrincipalRadius (g0 kappa rhoMax epsilon R MG : ℝ) (ell : ℕ) : ℝ :=
  min (kappa / 8) (modelCoercivityMargin g0 kappa rhoMax epsilon ell /
    (2 * (modelPrincipalRemainderBound ell R MG + 1)))

theorem modelPrincipalRemainderBound_nonneg (ell : ℕ) {R MG : ℝ}
    (hR : 0 ≤ R) (hMG : 0 ≤ MG) : 0 ≤ modelPrincipalRemainderBound ell R MG := by
  unfold modelPrincipalRemainderBound
  positivity

theorem modelPrincipalRadius_pos (ell : ℕ) {g0 kappa rhoMax epsilon R MG : ℝ}
    (hg0 : 0 < g0) (hkappa : 0 < kappa) (hrho : 0 < rhoMax) (heps : 0 < epsilon)
    (hR : 0 ≤ R) (hMG : 0 ≤ MG) :
    0 < modelPrincipalRadius g0 kappa rhoMax epsilon R MG ell := by
  have hmu := modelCoercivityMargin_pos ell hg0 hkappa hrho heps
  have hM := modelPrincipalRemainderBound_nonneg ell hR hMG
  unfold modelPrincipalRadius
  positivity

end SmoothLocal.Model

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MultiplierIntegral
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

def boxPoint (t s : ℝ) : Coord :=
  t • Pi.single 0 1 + s • Pi.single 1 1

def closedRectangle (tl tr sb st : ℝ) : Set Coord :=
  {p | p 0 ∈ Icc tl tr ∧ p 1 ∈ Icc sb st}

def rectangleIntegral (tl tr sb st : ℝ) (f : Coord → ℝ) : ℝ :=
  ∫ s in sb..st, ∫ t in tl..tr, f (boxPoint t s)

theorem boxPoint_mem {tl tr sb st t s : ℝ}
    (ht : t ∈ Icc tl tr) (hs : s ∈ Icc sb st) :
    boxPoint t s ∈ closedRectangle tl tr sb st := by
  simpa [boxPoint, closedRectangle] using And.intro ht hs

theorem boxPoint_hasDerivAt_t (t s : ℝ) :
    HasDerivAt (fun x => boxPoint x s) (Pi.single 0 (1 : ℝ) : Coord) t := by
  simpa [boxPoint] using
    ((hasDerivAt_id t).smul_const (Pi.single 0 (1 : ℝ) : Coord)).add_const
      (s • (Pi.single 1 (1 : ℝ) : Coord))

theorem boxPoint_hasDerivAt_s (t s : ℝ) :
    HasDerivAt (boxPoint t) (Pi.single 1 (1 : ℝ) : Coord) s := by
  change HasDerivAt (fun x : ℝ => t • (Pi.single 0 (1 : ℝ) : Coord) +
    x • (Pi.single 1 (1 : ℝ) : Coord)) (Pi.single 1 (1 : ℝ) : Coord) s
  simpa only [id_eq, one_smul] using
    ((hasDerivAt_id s).smul_const (Pi.single 1 (1 : ℝ) : Coord)).const_add
      (t • (Pi.single 0 (1 : ℝ) : Coord))

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

theorem rectangle_area_integrable
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    IntegrableOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Icc tl tr ×ˢ Icc sb st) :=
    hf.comp (by unfold boxPoint; fun_prop) (fun p hp => boxPoint_mem hp.1 hp.2)
  exact (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem rectangleIntegral_swap (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f =
      ∫ t in tl..tr, ∫ s in sb..st, f (boxPoint t s) := by
  have hi : IntegrableOn (Function.uncurry (fun t s => f (boxPoint t s)))
      (uIoc tl tr ×ˢ uIoc sb st) := by
    simpa only [uIoc_of_le ht, uIoc_of_le hs, Function.uncurry_def] using rectangle_area_integrable hf
  exact (intervalIntegral_intervalIntegral_swap hi).symm

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowExistence
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

def modelSquare : Set Coord := Icc (fun _ => (-3 : ℝ)) (fun _ => (3 : ℝ))

theorem modelSquare_isCompact : IsCompact modelSquare := isCompact_Icc

theorem coordinatePoint_mem_modelSquare {t y : ℝ}
    (ht : t ∈ Icc (-3 : ℝ) 3) (hy : y ∈ Icc (-3 : ℝ) 3) :
    coordinatePoint t y ∈ modelSquare := by
  simp only [mem_Icc] at ht hy
  constructor <;> intro i <;> fin_cases i <;> simp [coordinatePoint] <;> tauto

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def verticalAverageDerivative (q : Coord → ℝ) (t y0 y1 : ℝ) : ℝ :=
  ∫ u in 0..1, coordPartial 1 q (coordinatePoint t (y0 + u * (y1 - y0)))

theorem verticalSegment_mem_modelSquare {t y0 y1 u : ℝ}
    (ht : t ∈ Icc (-2 : ℝ) 2) (hy0 : y0 ∈ Icc (-3 : ℝ) 3)
    (hy1 : y1 ∈ Icc (-3 : ℝ) 3) (hu : u ∈ Icc (0 : ℝ) 1) :
    coordinatePoint t (y0 + u * (y1 - y0)) ∈ modelSquare := by
  apply coordinatePoint_mem_modelSquare
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hc := (convex_Icc (-3 : ℝ) 3) hy0 hy1
    (show 0 ≤ 1 - u by linarith [hu.2]) hu.1 (show (1 - u) + u = 1 by ring)
  have he : y0 + u * (y1 - y0) = (1 - u) * y0 + u * y1 := by ring
  rw [he]
  exact hc

theorem vertical_secant_identity {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {t y0 y1 : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2)
    (hy0 : y0 ∈ Icc (-3 : ℝ) 3) (hy1 : y1 ∈ Icc (-3 : ℝ) 3) :
    q (coordinatePoint t y1) - q (coordinatePoint t y0) =
      (y1 - y0) * verticalAverageDerivative q t y0 y1 := by
  let z (u : ℝ) := y0 + u * (y1 - y0)
  have hm (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) : coordinatePoint t (z u) ∈ U :=
    hSU (verticalSegment_mem_modelSquare ht hy0 hy1 hu)
  have hc : ContinuousOn (fun u => coordPartial 1 q (coordinatePoint t (z u)))
      (Icc (0 : ℝ) 1) :=
    (partial_contDiffOn hq hU 1).continuousOn.comp
      (by unfold coordinatePoint z; fun_prop) hm
  have hd (u : ℝ) (hu : u ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v => q (coordinatePoint t (z v)))
        (coordPartial 1 q (coordinatePoint t (z u)) * (y1 - y0)) u := by
    have hu' : u ∈ Icc (0 : ℝ) 1 := by simpa using hu
    have hqy := ((hq.contDiffAt (hU.mem_nhds (hm u hu'))).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt (z u) (coordinatePoint_hasDerivAt_y t (z u))
    have hz : HasDerivAt z (y1 - y0) u := by
      convert ((hasDerivAt_id u).mul_const (y1 - y0)).const_add y0 using 1 <;>
        first | rfl | ring
    convert hqy.comp u hz using 1 <;> rfl
  have hi : IntervalIntegrable
      (fun u => coordPartial 1 q (coordinatePoint t (z u))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using hc
  have hint : IntervalIntegrable
      (fun u => coordPartial 1 q (coordinatePoint t (z u)) * (y1 - y0)) volume 0 1 :=
    hi.mul_const (y1 - y0)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  rw [intervalIntegral.integral_mul_const] at hFTC
  have h0 : z 0 = y0 := by dsimp [z] <;> ring
  have h1 : z 1 = y1 := by dsimp [z] <;> ring
  rw [h0, h1] at hFTC
  unfold verticalAverageDerivative
  simpa only [z, mul_comm] using hFTC.symm

theorem verticalAverageDerivative_diagonal (q : Coord → ℝ) (t y : ℝ) :
    verticalAverageDerivative q t y y = coordPartial 1 q (coordinatePoint t y) := by
  simp [verticalAverageDerivative]

theorem flow_difference_hasDerivWithinAt {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {y0 y1 : ℝ → ℝ} {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2)
    (hy0 : y0 t ∈ Icc (-3 : ℝ) 3) (hy1 : y1 t ∈ Icc (-3 : ℝ) 3)
    (hdy0 : HasDerivWithinAt y0 (-q (coordinatePoint t (y0 t))) (Icc (-2 : ℝ) 2) t)
    (hdy1 : HasDerivWithinAt y1 (-q (coordinatePoint t (y1 t))) (Icc (-2 : ℝ) 2) t) :
    HasDerivWithinAt (fun v => y1 v - y0 v)
      (-verticalAverageDerivative q t (y0 t) (y1 t) * (y1 t - y0 t))
      (Icc (-2 : ℝ) 2) t := by
  have he := vertical_secant_identity hq hU hSU ht hy0 hy1
  convert hdy1.sub hdy0 using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | nlinarith only [he]

theorem scalar_linear_evolution_formula {a z : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (ha : ContinuousOn a (Ioo (-R) R))
    (hz : ∀ t ∈ Ioo (-R) R, HasDerivAt z (-a t * z t) t)
    {t : ℝ} (ht : t ∈ Ioo (-R) R) :
    z t = z 0 * Real.exp (-(∫ r in 0..t, a r)) := by
  let I (v : ℝ) := ∫ r in 0..v, a r
  have hzero : (0 : ℝ) ∈ Ioo (-R) R := ⟨by linarith, hR⟩
  have hI (v : ℝ) (hv : v ∈ Ioo (-R) R) : HasDerivAt I (a v) v := by
    have hseg : uIcc 0 v ⊆ Ioo (-R) R := by
      intro w hw
      exact ⟨(lt_min hzero.1 hv.1).trans_le hw.1,
        hw.2.trans_lt (max_lt hzero.2 hv.2)⟩
    exact intervalIntegral.integral_hasDerivAt_right (ha.mono hseg).intervalIntegrable
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo ha v hv)
      (ha.continuousAt (isOpen_Ioo.mem_nhds hv))
  have hprod (v : ℝ) (hv : v ∈ Ioo (-R) R) :
      HasDerivAt (fun w => z w * Real.exp (I w)) 0 v := by
    convert (hz v hv).mul ((hI v hv).exp) using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | ring
  have heq : z t * Real.exp (I t) = z 0 := by
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-R) R).isPreconnected
      (fun v hv => (hprod v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hprod v hv).deriv) ht hzero
    simpa [I] using hconst
  have he : Real.exp (I t) * Real.exp (-I t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    z t = (z t * Real.exp (I t)) * Real.exp (-I t) := by rw [mul_assoc, he, mul_one]
    _ = z 0 * Real.exp (-I t) := by rw [heq]
    _ = _ := rfl

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowParameterContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem continuous_intervalIntegral_of_joint
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {a b : ℝ} (hab : a ≤ b) {f : X → ℝ → ℝ}
    (hf : Continuous (fun p : X × Icc a b => f p.1 p.2)) :
    Continuous (fun x => ∫ u in a..b, f x u) := by
  let g : X → ℝ → ℝ := fun x u => f x (projIcc a b hab u)
  have hg : Continuous (uncurry g) :=
    hf.comp (continuous_fst.prodMk ((continuous_projIcc (h := hab)).comp continuous_snd))
  have hc : Continuous (fun x => ∫ u in Icc a b, g x u) :=
    continuous_parametric_integral_of_continuous hg isCompact_Icc
  apply hc.congr
  intro x
  calc
    (∫ u in Icc a b, g x u) = ∫ u in a..b, g x u := by
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    _ = ∫ u in a..b, f x u := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc a b := by simpa only [uIcc_of_le hab] using hu
      simp only [g, projIcc_of_mem hab hu']

abbrev CapInterval := Icc (-2 : ℝ) 2
abbrev VerticalInterval := Icc (-3 : ℝ) 3

theorem verticalAverageDerivative_continuous {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) :
    Continuous (fun p : CapInterval × (VerticalInterval × VerticalInterval) =>
      verticalAverageDerivative q p.1 p.2.1 p.2.2) := by
  apply continuous_intervalIntegral_of_joint (show (0 : ℝ) ≤ 1 by norm_num)
  have hmap : Continuous
      (fun p : (CapInterval × (VerticalInterval × VerticalInterval)) × Icc (0 : ℝ) 1 =>
        coordinatePoint p.1.1 ((p.1.2.1 : ℝ) + p.2 * ((p.1.2.2 : ℝ) - p.1.2.1))) := by
    unfold coordinatePoint
    fun_prop
  exact (partial_contDiffOn hq hU 1).continuousOn.comp_continuous hmap
    (fun p => hSU (verticalSegment_mem_modelSquare p.1.1.2 p.1.2.1.2 p.1.2.2.2 p.2.2))

def flowAverageCoefficient (q : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (s0 s1 t : ℝ) : ℝ :=
  verticalAverageDerivative q t (Y s0 t) (Y s1 t)

theorem flowAverageCoefficient_continuous {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {Y : ℝ → ℝ → ℝ}
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3) :
    Continuous (fun p : CapInterval × (CapInterval × CapInterval) =>
      flowAverageCoefficient q Y p.1 p.2.1 p.2.2) := by
  have hy0 : Continuous (fun p : CapInterval × (CapInterval × CapInterval) =>
      Y p.1 p.2.2) :=
    hY.comp_continuous
      (f := fun p : CapInterval × (CapInterval × CapInterval) => ((p.1 : ℝ), (p.2.2 : ℝ)))
      (by fun_prop) (fun p => ⟨p.1.2, p.2.2.2⟩)
  have hy1 : Continuous (fun p : CapInterval × (CapInterval × CapInterval) =>
      Y p.2.1 p.2.2) :=
    hY.comp_continuous
      (f := fun p : CapInterval × (CapInterval × CapInterval) => ((p.2.1 : ℝ), (p.2.2 : ℝ)))
      (by fun_prop) (fun p => ⟨p.2.1.2, p.2.2.2⟩)
  have hmap : Continuous
      (fun p : CapInterval × (CapInterval × CapInterval) =>
        (p.2.2, ((⟨Y p.1 p.2.2, hrange _ p.1.2 _ p.2.2.2⟩,
          ⟨Y p.2.1 p.2.2, hrange _ p.2.1.2 _ p.2.2.2⟩) :
          VerticalInterval × VerticalInterval))) :=
    (continuous_snd.snd).prodMk
      ((hy0.subtype_mk _).prodMk (hy1.subtype_mk _))
  exact (verticalAverageDerivative_continuous hq hU hSU).comp hmap

theorem flowAverageIntegral_continuous {q : Coord → ℝ} {U : Set Coord}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    {Y : ℝ → ℝ → ℝ}
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3) {t : ℝ} (ht : t ∈ Icc (-2 : ℝ) 2) :
    Continuous (fun p : CapInterval × CapInterval =>
      ∫ u in 0..t, flowAverageCoefficient q Y p.1 p.2 u) := by
  have hcoeff := flowAverageCoefficient_continuous hq hU hSU hY hrange
  have haux (a b : ℝ) (hab : a ≤ b) (ha : -2 ≤ a) (hb : b ≤ 2) :
      Continuous (fun p : CapInterval × CapInterval =>
        ∫ u in a..b, flowAverageCoefficient q Y p.1 p.2 u) := by
    apply continuous_intervalIntegral_of_joint hab
    have hmap : Continuous
        (fun p : (CapInterval × CapInterval) × Icc a b =>
          (p.1.1, (p.1.2, (⟨p.2, ⟨ha.trans p.2.2.1, p.2.2.2.trans hb⟩⟩ : CapInterval)))) := by
      fun_prop
    exact hcoeff.comp hmap
  by_cases ht0 : 0 ≤ t
  · exact haux 0 t ht0 (by norm_num) ht.2
  · have hc := (haux t 0 (le_of_not_ge ht0) ht.1 (by norm_num)).neg
    apply hc.congr
    intro p
    exact (intervalIntegral.integral_symm _ _).symm

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Metric Filter Function MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem hasDerivAt_of_exact_secant {f g : ℝ → ℝ} {s : ℝ}
    (hg : ContinuousAt g s)
    (he : ∀ᶠ u in 𝓝 s, f u - f s = (u - s) * g u) :
    HasDerivAt f (g s) s := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : slope f s =ᶠ[𝓝[≠] s] g := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hne
    have hne' : u ≠ s := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
    rw [slope_def_field, hu]
    exact mul_div_cancel_left₀ (g u) (sub_ne_zero.mpr hne')
  exact (hg.mono_left nhdsWithin_le_nhds).congr' hslope.symm

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem flow_difference_formula
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {s0 s1 t : ℝ} (hs0 : s0 ∈ Icc (-2 : ℝ) 2) (hs1 : s1 ∈ Icc (-2 : ℝ) 2)
    (ht : t ∈ Ioo (-2 : ℝ) 2) :
    Y s1 t - Y s0 t = (s1 - s0) *
      Real.exp (-(∫ u in 0..t, flowAverageCoefficient q Y s0 s1 u)) := by
  have hcoeff := flowAverageCoefficient_continuous hq hU hSU hY hrange
  have ha : ContinuousOn (flowAverageCoefficient q Y s0 s1) (Icc (-2 : ℝ) 2) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hcoeff.comp
      ((continuous_const (y := (⟨s0, hs0⟩ : CapInterval))).prodMk
        ((continuous_const (y := (⟨s1, hs1⟩ : CapInterval))).prodMk continuous_id))
  have hz (u : ℝ) (hu : u ∈ Ioo (-2 : ℝ) 2) :
      HasDerivAt (fun v => Y s1 v - Y s0 v)
        (-flowAverageCoefficient q Y s0 s1 u * (Y s1 u - Y s0 u)) u := by
    exact (flow_difference_hasDerivWithinAt hq hU hSU ⟨hu.1.le, hu.2.le⟩
      (hrange s0 hs0 u ⟨hu.1.le, hu.2.le⟩) (hrange s1 hs1 u ⟨hu.1.le, hu.2.le⟩)
      (hode s0 hs0 u ⟨hu.1.le, hu.2.le⟩) (hode s1 hs1 u ⟨hu.1.le, hu.2.le⟩)).hasDerivAt
        (Icc_mem_nhds hu.1 hu.2)
  have he := scalar_linear_evolution_formula (show (0 : ℝ) < 2 by norm_num)
    (ha.mono Ioo_subset_Icc_self) hz ht
  simpa only [hstart s0 hs0, hstart s1 hs1] using he

theorem cap_flow_hasDerivAt_initial
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (fun u => Y u t)
      (Real.exp (-(∫ r in 0..t, coordPartial 1 q (coordinatePoint r (Y s r))))) s := by
  let G (u : ℝ) := Real.exp (-(∫ r in 0..t, flowAverageCoefficient q Y s u r))
  have hG : ContinuousOn G (Icc (-2 : ℝ) 2) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (((flowAverageIntegral_continuous hq hU hSU hY hrange
      ⟨ht.1.le, ht.2.le⟩).comp
        ((continuous_const (y := (⟨s, ⟨hs.1.le, hs.2.le⟩⟩ : CapInterval))).prodMk continuous_id)).neg).rexp
  have he : ∀ᶠ u in 𝓝 s, Y u t - Y s t = (u - s) * G u := by
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with u hu
    exact flow_difference_formula hq hU hSU hY hrange hstart hode ⟨hs.1.le, hs.2.le⟩ hu ht
  have hd := hasDerivAt_of_exact_secant (hG.continuousAt (Icc_mem_nhds hs.1 hs.2)) he
  have hdiag : G s = Real.exp (-(∫ r in 0..t,
      coordPartial 1 q (coordinatePoint r (Y s r)))) := by
    simp only [G, flowAverageCoefficient, verticalAverageDerivative_diagonal]
  rw [hdiag] at hd
  exact hd

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowJointSmooth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def flowCoordinateMap (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : Coord :=
  coordinatePoint p.1 (Y p.2 p.1)

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem cap_flow_joint_contDiffOn
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2) := by
  let D := pairRectangle 2 (-2) 2
  let F (p : ℝ × ℝ) := Y p.2 p.1
  let B (p : ℝ × ℝ) := coordPartial 1 q (flowCoordinateMap Y p)
  have hmem : MapsTo (flowCoordinateMap Y) D U := by
    intro p hp
    exact hSU (coordinatePoint_mem_modelSquare
      ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
      (hrange p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩))
  have hdx (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun x => F (x, p.2)) (-q (flowCoordinateMap Y p)) p.1 := by
    exact (hode p.2 ⟨hp.2.1.le, hp.2.2.le⟩ p.1 ⟨hp.1.1.le, hp.1.2.le⟩).hasDerivAt
      (Icc_mem_nhds hp.1.1 hp.1.2)
  have hdy (p : ℝ × ℝ) (hp : p ∈ D) :
      HasDerivAt (fun y => F (p.1, y)) (Real.exp (-pairPrimitive B p)) p.2 := by
    exact cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hp.2 hp.1
  have hnat : ∀ n : ℕ, ContDiffOn ℝ n F D := by
    intro n
    induction n with
    | zero =>
        have hc : ContinuousOn F D := hY.comp continuous_swap.continuousOn
          (fun p hp => ⟨⟨hp.2.1.le, hp.2.2.le⟩, ⟨hp.1.1.le, hp.1.2.le⟩⟩)
        simpa only [Nat.cast_zero, contDiffOn_zero] using hc
    | succ n hn =>
        have horder : (n : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
        have hmap : ContDiffOn ℝ n (flowCoordinateMap Y) D := by
          exact (contDiffOn_fst.smul contDiffOn_const).add (hn.smul contDiffOn_const)
        have hfx : ContDiffOn ℝ n (fun p => -q (flowCoordinateMap Y p)) D :=
          ((hq.of_le horder).comp hmap hmem).neg
        have hB : ContDiffOn ℝ n B D :=
          ((partial_contDiffOn hq hU 1).of_le horder).comp hmap hmem
        have hfy : ContDiffOn ℝ n (fun p => Real.exp (-pairPrimitive B p)) D :=
          ((pairPrimitive_contDiffOn_nat n hB).neg).exp
        exact contDiffOn_succ_of_continuous_partials (pairRectangle_isOpen 2 (-2) 2) n
          hfx hfy hdx hdy
  exact contDiffOn_infty.mpr hnat

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowCurvature
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

def capChartDomain : Set Coord := coordinateRectangle 2 (-2) 2

def capFlowHeight (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ := Y (p 1) (p 0)

def capChart (Y : ℝ → ℝ → ℝ) (p : Coord) : Coord :=
  coordinatePoint (p 0) (capFlowHeight Y p)

theorem capChart_zero (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 0 = p 0 := by
  simp [capChart, coordinatePoint]

theorem capChart_one (Y : ℝ → ℝ → ℝ) (p : Coord) : capChart Y p 1 = capFlowHeight Y p := by
  simp [capChart, coordinatePoint]

variable {Y : ℝ → ℝ → ℝ}

theorem capFlowHeight_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capFlowHeight Y) capChartDomain := by
  exact hY.comp ((contDiffOn_apply ℝ ℝ 0 _).prodMk (contDiffOn_apply ℝ ℝ 1 _))
    (fun p hp => hp)

theorem capChart_contDiffOn
    (hY : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)) :
    ContDiffOn ℝ ∞ (capChart Y) capChartDomain := by
  exact ((contDiffOn_apply ℝ ℝ 0 _).smul contDiffOn_const).add
    ((capFlowHeight_contDiffOn hY).smul contDiffOn_const)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ChainTermDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.HighEquation

structure ChainWord where
  arity : ℕ
  order : Fin arity → ℕ

def ChainWord.prepend (w : ChainWord) : ChainWord :=
  ⟨w.arity + 1, Fin.cons 1 w.order⟩

def ChainWord.bump (w : ChainWord) (i : Fin w.arity) : ChainWord :=
  ⟨w.arity, Function.update w.order i (w.order i + 1)⟩

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_ChainResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.HighEquation

def ChainWord.pair (a b : ℕ) : ChainWord := ⟨2, ![a, b]⟩
def ChainWord.triple (a b c : ℕ) : ChainWord := ⟨3, ![a, b, c]⟩

def ChainWord.children (w : ChainWord) : List ChainWord :=
  w.prepend :: List.ofFn w.bump

def topResidualWords : ℕ → List ChainWord
  | 0 => [ChainWord.triple 1 1 1]
  | m + 1 =>
      (topResidualWords m).flatMap ChainWord.children ++
        List.replicate (m + 3) (ChainWord.triple 1 1 (m + 2)) ++
        List.replicate (m + 3) (ChainWord.pair 2 (m + 2))

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_SecondJetExtraction
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

def firstJetPairRemainder (g : MetricField) (z : Coord → ℝ) (n : ℕ) (p : Coord) : ℝ :=
  coordPartial 1 (heightPFirst g z 0) p * coordPartial 0 (verticalJet z n) p +
  coordPartial 1 (heightPFirst g z 1) p * coordPartial 1 (verticalJet z n) p

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticCutoff
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

theorem smoothTransition_deriv_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.smoothTransition.zero_of_nonpos hx]
    exact Real.smoothTransition.nonneg y)

theorem smoothTransition_deriv_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    deriv Real.smoothTransition x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  exact Filter.Eventually.of_forall (fun y => by
    rw [Real.smoothTransition.one_of_one_le hx]
    exact Real.smoothTransition.le_one y)

theorem exists_smoothTransition_derivative_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ M := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  by_cases hx : x ≤ 0
  · rw [smoothTransition_deriv_zero_of_nonpos hx, abs_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  by_cases hx1 : 1 ≤ x
  · rw [smoothTransition_deriv_zero_of_one_le hx1, abs_zero]
    exact le_trans zero_le_one (le_max_left _ _)
  have hxc : x ∈ Icc (0 : ℝ) 1 := ⟨(lt_of_not_ge hx).le, (lt_of_not_ge hx1).le⟩
  have hcx : |deriv Real.smoothTransition x| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC x hxc
  exact hcx.trans (le_max_right _ _)

def transitionDerivativeBound : ℝ :=
  Classical.choose exists_smoothTransition_derivative_bound

def capInnerEdge (x : ℝ) : ℝ := (-2 + min x (-3 / 2)) / 2
def capOuterEdge (x : ℝ) : ℝ := (-2 + capInnerEdge x) / 2

theorem capEdges_bounds {x : ℝ} (hx : -2 < x) :
    -2 < capOuterEdge x ∧ capOuterEdge x < capInnerEdge x ∧
      capInnerEdge x < -3 / 2 ∧ capInnerEdge x < x := by
  have hm : -2 < min x (-3 / 2 : ℝ) := lt_min hx (by norm_num)
  have hmx := min_le_left x (-3 / 2 : ℝ)
  have hmh := min_le_right x (-3 / 2 : ℝ)
  unfold capInnerEdge capOuterEdge
  dsimp only [capInnerEdge]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticRatio
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

def ellipticRatioConstant (D c Cv M : ℝ) : ℝ :=
  2 * (1 + M) * Cv ^ 2 * (D ^ 2 + D ^ 3) ^ 2 +
    2 * D ^ 6 * M ^ 2 + 8 * D ^ 5 * M ^ 2 / c

def ellipticCutoffDerivativeConstant (c MK X : ℝ) : ℝ :=
  2 * (3 + X + (2 * transitionDerivativeBound / c) * (MK + c))

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticApplication
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

def threeEdgeDerivativeConstant (l0 l1 r1 r0 a0 a1 : ℝ) : ℝ :=
  transitionDerivativeBound / (l1 - l0) + transitionDerivativeBound / (r0 - r1) +
    transitionDerivativeBound / (a1 - a0)

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapEllipticOverlap
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

def capOverlapThreshold (kappa c1 D : ℝ) : ℝ := min c1 (kappa / (D + 1))

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedFluxCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def capSpatialDerivativeConstant (L R A : ℝ) : ℝ :=
  threeEdgeDerivativeConstant (capOuterEdge L) (capInnerEdge L)
    (-capInnerEdge (-R)) (-capOuterEdge (-R)) (capOuterEdge A) (capInnerEdge A)

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedWeightJetCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedWeightJetBudget (D M lambda : ℝ) : ℝ := 16 + 3*D + 2*D*(M+lambda)

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedDefectCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedQuadraticCostConstant (D M lambda S MI : ℝ) : ℝ :=
  (2+8*M)*directedWeightJetBudget D M lambda*Real.exp (lambda*S+MI)

def directedDefectCostConstant (D M lambda S MI c2 : ℝ) : ℝ :=
  c2*D*Real.exp (lambda*S+MI) + directedQuadraticCostConstant D M lambda S MI

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapOverlapCosts
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

def directedFluxCostConstant (D M lambda S MI X : ℝ) : ℝ :=
  6*X*D*Real.exp (lambda*S+MI)*(M+1)

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapCutoffRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

def capOuterLeft (L : ℝ) : ℝ := capOuterEdge (capOuterEdge L)
def capOuterLeftOne (L : ℝ) : ℝ := capInnerEdge (capOuterEdge L)
def capOuterRightOne (R : ℝ) : ℝ := -capInnerEdge (capOuterEdge (-R))
def capOuterRight (R : ℝ) : ℝ := -capOuterEdge (capOuterEdge (-R))
def capOuterBottom (A : ℝ) : ℝ := capOuterEdge (capOuterEdge A)
def capOuterBottomOne (A : ℝ) : ℝ := capInnerEdge (capOuterEdge A)

theorem capOuterRectangle_edges {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) :
    -2 < capOuterLeft L ∧ capOuterLeft L < capOuterLeftOne L ∧ capOuterLeftOne L < -3/2 ∧
    3/2 < capOuterRightOne R ∧ capOuterRightOne R < capOuterRight R ∧ capOuterRight R < 2 ∧
    -2 < capOuterBottom A ∧ capOuterBottom A < capOuterBottomOne A ∧
    capOuterBottomOne A < A ∧ capOuterLeft L < L ∧ R < capOuterRight R := by
  obtain ⟨hlo,hli,hlu,hlx⟩ := capEdges_bounds hL
  obtain ⟨hro,hri,hru,hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao,hai,hau,hax⟩ := capEdges_bounds hA
  obtain ⟨hloo,hlio,hluo,hlxo⟩ := capEdges_bounds hlo
  obtain ⟨hroo,hrio,hruo,hrxo⟩ := capEdges_bounds hro
  obtain ⟨haoo,haio,hauo,haxo⟩ := capEdges_bounds hao
  unfold capOuterLeft capOuterLeftOne capOuterRightOne capOuterRight capOuterBottom capOuterBottomOne
  refine ⟨hloo,hlio,hluo,?_,?_,?_,haoo,haio,?_,?_,?_⟩ <;> linarith

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_IntegratedCapOverlap
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

def capDistanceBound (A b : ℝ) : ℝ := b-capOuterBottom A

def capOverlapEnergyCost (L R A b kappa c1 c2 glow M lambda MI : ℝ) : ℝ :=
  let D := capDistanceBound A b
  let c := capOverlapThreshold kappa c1 D
  (directedFluxCostConstant D M lambda 2 MI (capSpatialDerivativeConstant L R A) +
    directedDefectCostConstant D M lambda 2 MI c2)*(D+1/(glow*c))

def capEllipticRatioBudget (L R A b kappa c1 glow MK M : ℝ) : ℝ :=
  let D := capDistanceBound A b
  let c := capOverlapThreshold kappa c1 D
  ellipticRatioConstant D (glow*c/2)
    (ellipticCutoffDerivativeConstant c MK
      (threeEdgeDerivativeConstant (capOuterLeft L) (capOuterLeftOne L) (capOuterRightOne R)
        (capOuterRight R) (capOuterBottom A) (capOuterBottomOne A))) M

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapInteriorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.Flow

def capInteriorWeightFloor (top b lambda MI : ℝ) : ℝ :=
  (b-top)^8*Real.exp (-lambda*top-MI)

end SmoothLocal.Weighted

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

def coordinateChainTerm (g : MetricField) (z : Coord → ℝ) (w : ChainWord) (p : Coord) : ℝ :=
  iteratedFDeriv ℝ w.arity (sixVariableP g) (solutionJet z p)
    (fun i => verticalJet (solutionJet z) (w.order i) p)

def coordinateChainSum (g : MetricField) (z : Coord → ℝ) (ws : List ChainWord) (p : Coord) : ℝ :=
  (ws.map (fun w => coordinateChainTerm g z w p)).sum

def actualHighRemainder (g : MetricField) (z : Coord → ℝ) (m : ℕ) (p : Coord) : ℝ :=
  coordinateChainSum g z (topResidualWords m) p +
    (m + 3 : ℝ) * firstJetPairRemainder g z (m + 2) p

end SmoothLocal.HighEquation

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

def modelOpenSquare : Set Coord := coordinateRectangle 3 (-3) 3

theorem modelOpenSquare_subset : modelOpenSquare ⊆ modelSquare := by
  intro p hp
  constructor <;> intro i <;> fin_cases i
  · exact hp.1.1.le
  · exact hp.2.1.le
  · exact hp.1.2.le
  · exact hp.2.2.le

theorem capChart_mem_modelOpenSquare {Y : ℝ → ℝ → ℝ} {p : Coord}
    (hp : p ∈ capChartDomain) (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) :
    capChart Y p ∈ modelOpenSquare := by
  change (capChart Y p) 0 ∈ Ioo (-3 : ℝ) 3 ∧ (capChart Y p) 1 ∈ Ioo (-3 : ℝ) 3
  rw [capChart_zero, capChart_one]
  constructor
  · constructor <;> linarith [hp.1.1, hp.1.2]
  · constructor <;> linarith [hp.2.1, hp.2.2, (abs_le.mp hdisp).1, (abs_le.mp hdisp).2]

end SmoothLocal.Flow

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

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def directedPrincipalBound (ell : ℕ) (epsilon R MAs MAt : ℝ) : ℝ :=
  ((ell : ℝ) + 1 / 2) * MAs + epsilon * R * MAt / 2

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedParameterChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Model

theorem exists_directed_parameters (ell : ℕ)
    {kappa cG rhoMax MG MI MB Mr MA MAs MAt MG1 D : ℝ}
    (hk : 0 < kappa) (hcG : 0 < cG) (hrho : 0 < rhoMax)
    (hMG : 0 ≤ MG) (hMI : 0 ≤ MI) (hMB : 0 ≤ MB) (hMr : 0 ≤ Mr)
    (hMA : 0 ≤ MA) (hMAs : 0 ≤ MAs) (hMAt : 0 ≤ MAt) (hMG1 : 0 ≤ MG1) (hD : 0 ≤ D) :
    ∃ epsilon lambda c1 : ℝ,
      0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧
      epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax ∧
      2 * (MI + epsilon + epsilon * 2 * MB) ≤ lambda ∧
      (MI + 1 + 2 * MB) / 2 + Mr ≤ lambda / 8 ∧
      4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2 * MA ≤ 1 / 8 ∧
      (4 * (2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1))^2 * epsilon^2) / lambda ≤
        modelCoercivityMargin cG kappa rhoMax epsilon ell / 8 ∧
      directedPrincipalBound ell epsilon 2 MAs MAt + modelCoercivityMargin cG kappa rhoMax epsilon ell / 2 ≤
        lambda * (cG * modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell) / 4 ∧
      c1 * D ≤ modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell ∧
      MG1 * c1 * (lambda * D + 8) ≤ modelCoercivityMargin cG kappa rhoMax epsilon ell / 6 := by
  let Cj := 2 * ((ell : ℝ) * MAs + MA * Mr + MA * MI + 1)
  let L := 4 * Cj^2
  have hCj : 0 ≤ Cj := by dsimp [Cj] <;> positivity
  have hL : 0 ≤ L := by dsimp [L] <;> positivity
  have hbeta : 0 < ((ell : ℝ) + 1 / 2) / rhoMax := by positivity
  have hden : 0 < 8 * L * MA + 1 := by positivity
  let epsilon := min 1 (min (((ell : ℝ) + 1 / 2) / rhoMax) (1 / (8 * L * MA + 1)))
  have heps : 0 < epsilon := by dsimp [epsilon] <;> positivity
  have heps1 : epsilon ≤ 1 := min_le_left _ _
  have hepsbeta : epsilon ≤ ((ell : ℝ) + 1 / 2) / rhoMax :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hepsden : epsilon ≤ 1 / (8 * L * MA + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hcross : L * epsilon^2 * MA ≤ 1 / 8 := by
    have hm := (le_div_iff₀ hden).mp hepsden
    have hsquare : epsilon^2 ≤ epsilon := by nlinarith only [heps.le, heps1]
    have hprod := mul_le_mul_of_nonneg_left hsquare (mul_nonneg hL hMA)
    nlinarith only [hm, hprod, heps.le]
  have hqbudget : epsilon * 2 * ((1 : ℝ) / 100) ≤ ((ell : ℝ) + 1 / 2) / rhoMax := by
    have hh : epsilon * 2 * ((1 : ℝ) / 100) ≤ epsilon := by linarith only [heps.le]
    exact hh.trans hepsbeta
  let margin := modelCoercivityMargin cG kappa rhoMax epsilon ell
  let delta := modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell
  let alpha := cG * delta
  have hmargin : 0 < margin := modelCoercivityMargin_pos ell hcG hk hrho heps
  have hdelta : 0 < delta := modelPrincipalRadius_pos ell hcG hk hrho heps (by norm_num) hMG
  have halpha : 0 < alpha := mul_pos hcG hdelta
  let T0 := 2 * (MI + 1 + 2 * MB)
  let E0 := (MI + 1 + 2 * MB) / 2 + Mr
  let P0 := ((ell : ℝ) + 1 / 2) * MAs + MAt
  have hT0 : 0 ≤ T0 := by dsimp [T0] <;> positivity
  have hE0 : 0 ≤ E0 := by dsimp [E0] <;> positivity
  have hP0 : 0 ≤ P0 := by dsimp [P0] <;> positivity
  let lambda := 1 + T0 + 8 * E0 + 8 * L * epsilon^2 / margin + 4 * (P0 + margin / 2) / alpha
  have hLterm : 0 ≤ 8 * L * epsilon^2 / margin := by positivity
  have hFterm : 0 ≤ 4 * (P0 + margin / 2) / alpha := by positivity
  have hlambda : 0 < lambda := by dsimp [lambda]; linarith only [hT0, hE0, hLterm, hFterm]
  have hTlambda : T0 ≤ lambda := by dsimp [lambda]; linarith only [hE0, hLterm, hFterm]
  have hElambda : 8 * E0 ≤ lambda := by dsimp [lambda]; linarith only [hT0, hLterm, hFterm]
  have hLlambda : 8 * L * epsilon^2 / margin ≤ lambda := by dsimp [lambda]; linarith only [hT0, hE0, hFterm]
  have hFlambda : 4 * (P0 + margin / 2) / alpha ≤ lambda := by dsimp [lambda]; linarith only [hT0, hE0, hLterm]
  have hTbudget : 2 * (MI + epsilon + epsilon * 2 * MB) ≤ lambda := by
    have hp := mul_le_mul_of_nonneg_right heps1 (show 0 ≤ 2 * MB by positivity)
    have hh : 2 * (MI + epsilon + epsilon * 2 * MB) ≤ T0 := by dsimp [T0]; nlinarith only [hp, heps1]
    exact hh.trans hTlambda
  have hEbudget : E0 ≤ lambda / 8 := by linarith only [hElambda]
  have hloss : L * epsilon^2 / lambda ≤ margin / 8 := by
    have hh := (div_le_iff₀ hmargin).mp hLlambda
    apply (div_le_iff₀ hlambda).mpr
    nlinarith only [hh]
  have hprincipal : directedPrincipalBound ell epsilon 2 MAs MAt ≤ P0 := by
    have hh := mul_le_mul_of_nonneg_right heps1 hMAt
    dsimp [directedPrincipalBound, P0]
    nlinarith only [hh]
  have hfar : directedPrincipalBound ell epsilon 2 MAs MAt + margin / 2 ≤ lambda * alpha / 4 := by
    have hh := (div_le_iff₀ halpha).mp hFlambda
    nlinarith only [hh, hprincipal]
  have hD1 : 0 < D + 1 := by linarith only [hD]
  have hstripden : 0 < 6 * (MG1 + 1) * (lambda * D + 8) := by positivity
  let c1 := min (delta / (D + 1)) (margin / (6 * (MG1 + 1) * (lambda * D + 8)))
  have hc1 : 0 < c1 := by dsimp [c1] <;> positivity
  have hc1delta : c1 ≤ delta / (D + 1) := min_le_left _ _
  have hc1strip : c1 ≤ margin / (6 * (MG1 + 1) * (lambda * D + 8)) := min_le_right _ _
  have hnearstrip : c1 * D ≤ delta := by
    have hh := (le_div_iff₀ hD1).mp hc1delta
    nlinarith only [hh, hc1.le]
  have hstrip : MG1 * c1 * (lambda * D + 8) ≤ margin / 6 := by
    have hh := (le_div_iff₀ hstripden).mp hc1strip
    have hfac : 0 ≤ c1 * (lambda * D + 8) := by positivity
    have hbase : MG1 * c1 * (lambda * D + 8) ≤ (MG1 + 1) * c1 * (lambda * D + 8) := by
      nlinarith only [hfac]
    have hfull : (MG1 + 1) * c1 * (lambda * D + 8) ≤ margin / 6 := by nlinarith only [hh]
    exact hbase.trans hfull
  exact ⟨epsilon, lambda, c1, heps, heps1, hlambda, hc1, hqbudget, hTbudget,
    hEbudget, hcross, hloss, hfar, hnearstrip, hstrip⟩

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}

theorem flow_initial_integral_bound
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    {M : ℝ} (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Icc (-2 : ℝ) 2) (ht : t ∈ Icc (-2 : ℝ) 2) :
    IntervalIntegrable (fun r => coordPartial 1 q (coordinatePoint r (Y s r))) volume 0 t ∧
      |∫ r in 0..t, coordPartial 1 q (coordinatePoint r (Y s r))| ≤ 2 * M := by
  have hmem (u : ℝ) (hu : u ∈ Icc (-2 : ℝ) 2) :
      coordinatePoint u (Y s u) ∈ modelSquare :=
    coordinatePoint_mem_modelSquare ⟨by linarith [hu.1], by linarith [hu.2]⟩ (hrange s hs u hu)
  have hy : ContinuousOn (Y s) (Icc (-2 : ℝ) 2) :=
    hY.comp (f := fun u : ℝ => (s, u)) (by fun_prop) (fun u hu => ⟨hs, hu⟩)
  have hmap : ContinuousOn (fun u => coordinatePoint u (Y s u)) (Icc (-2 : ℝ) 2) :=
    (continuousOn_id.smul continuousOn_const).add (hy.smul continuousOn_const)
  have hc : ContinuousOn (fun u => coordPartial 1 q (coordinatePoint u (Y s u)))
      (Icc (-2 : ℝ) 2) :=
    (partial_contDiffOn hq hU 1).continuousOn.comp hmap (fun u hu => hSU (hmem u hu))
  have hseg : uIcc (0 : ℝ) t ⊆ Icc (-2 : ℝ) 2 :=
    uIcc_subset_Icc ⟨by norm_num, by norm_num⟩ ht
  refine ⟨(hc.mono hseg).intervalIntegrable, ?_⟩
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := M)
    (f := fun u => coordPartial 1 q (coordinatePoint u (Y s u)))
    (fun u hu => by
      rw [Real.norm_eq_abs]
      exact hMq _ (hmem u (hseg (uIoc_subset_uIcc hu))))
  have ht2 : |t| ≤ 2 := abs_le.mpr ht
  calc
    _ ≤ M * |t| := by simpa only [Real.norm_eq_abs, sub_zero] using hh
    _ ≤ M * 2 := mul_le_mul_of_nonneg_left ht2 hM
    _ = 2 * M := mul_comm _ _

theorem cap_flow_initial_deriv_bounds
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {M : ℝ} (hM : 0 ≤ M) (hMq : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    Real.exp (-2 * M) ≤ deriv (fun u => Y u t) s ∧
      deriv (fun u => Y u t) s ≤ Real.exp (2 * M) := by
  have hI := (flow_initial_integral_bound hq hU hSU hY hrange hM hMq
    ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩).2
  rw [(cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).deriv]
  constructor
  · apply Real.exp_monotone
    linarith [(abs_le.mp hI).2]
  · apply Real.exp_monotone
    linarith [(abs_le.mp hI).1]

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowSecondVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem flowCoordinateMap_mem_modelSquare {p : ℝ × ℝ}
    (hp : p ∈ pairRectangle 2 (-2) 2) : flowCoordinateMap Y p ∈ modelSquare := by
  have hF := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hbound : Y p.2 p.1 ∈ Icc (-3 : ℝ) 3 := by
    apply isClosed_Icc.mem_of_tendsto
      (hF.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds hp)).continuousAt
    filter_upwards [(pairRectangle_isOpen 2 (-2) 2).mem_nhds hp] with point hpoint
    exact hrange point.2 ⟨hpoint.2.1.le, hpoint.2.2.le⟩
      point.1 ⟨hpoint.1.1.le, hpoint.1.2.le⟩
  exact coordinatePoint_mem_modelSquare ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩
    hbound

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowTimeVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def timeFlowDerivative (Y : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ := deriv (Y p.2) p.1

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem cap_flow_time_hasDerivAt {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    HasDerivAt (Y s) (-q (coordinatePoint t (Y s t))) t := by
  have hsmooth := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have htime : DifferentiableAt ℝ (Y s) t :=
    ((hsmooth.contDiffAt ((pairRectangle_isOpen 2 (-2) 2).mem_nhds ⟨ht, hs⟩)).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp t (differentiableAt_id.prodMk (differentiableAt_const s))
  have hderiv := (hode s ⟨hs.1.le, hs.2.le⟩ t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  simpa only [hderiv.deriv] using htime.hasDerivAt

theorem timeFlowDerivative_eq {s t : ℝ}
    (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    timeFlowDerivative Y (t, s) = -q (coordinatePoint t (Y s t)) :=
  (cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).deriv

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowLowBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory Function
open scoped ContDiff Topology Interval

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

section ActualFlow
variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem cap_flow_time_bound
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    {s t : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2) (ht : t ∈ Ioo (-2 : ℝ) 2) :
    |timeFlowDerivative Y (t, s)| ≤ (1 : ℝ) / 100 := by
  rw [timeFlowDerivative_eq hq hU hSU hY hrange hstart hode hs ht, abs_neg]
  exact hq0 _ (flowCoordinateMap_mem_modelSquare (p := (t, s)) hq hU hSU hY hrange hstart hode ⟨ht, hs⟩)

end ActualFlow
end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapFlowJetBounds
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

def flowCoordinateBound (M : ℝ) : ℝ :=
  4 + Real.exp (2 * M) + 2 * M + M * Real.exp (2 * M) + 2 * M * Real.exp (4 * M) +
    (4 * M + 2 * M^2) + (2 * M + M^2) * Real.exp (2 * M) +
    (M + 2 * M^2) * Real.exp (4 * M) + (2 * M + 8 * M^2) * Real.exp (6 * M)

theorem flowCoordinateBound_dominates {M : ℝ} (hM : 0 ≤ M) :
    3 ≤ flowCoordinateBound M ∧ 1 ≤ flowCoordinateBound M ∧
    Real.exp (2 * M) ≤ flowCoordinateBound M ∧ 2 * M ≤ flowCoordinateBound M ∧
    M * Real.exp (2 * M) ≤ flowCoordinateBound M ∧ 2 * M * Real.exp (4 * M) ≤ flowCoordinateBound M ∧
    4 * M + 2 * M^2 ≤ flowCoordinateBound M ∧
    (2 * M + M^2) * Real.exp (2 * M) ≤ flowCoordinateBound M ∧
    (M + 2 * M^2) * Real.exp (4 * M) ≤ flowCoordinateBound M ∧
    (2 * M + 8 * M^2) * Real.exp (6 * M) ≤ flowCoordinateBound M := by
  have h1 : 0 ≤ Real.exp (2 * M) := (Real.exp_pos _).le
  have h2 : 0 ≤ 2 * M := by positivity
  have h3 : 0 ≤ M * Real.exp (2 * M) := by positivity
  have h4 : 0 ≤ 2 * M * Real.exp (4 * M) := by positivity
  have h5 : 0 ≤ 4 * M + 2 * M^2 := by positivity
  have h6 : 0 ≤ (2 * M + M^2) * Real.exp (2 * M) := by positivity
  have h7 : 0 ≤ (M + 2 * M^2) * Real.exp (4 * M) := by positivity
  have h8 : 0 ≤ (2 * M + 8 * M^2) * Real.exp (6 * M) := by positivity
  dsimp [flowCoordinateBound]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem flowCoordinateBound_nonneg {M : ℝ} (hM : 0 ≤ M) : 0 ≤ flowCoordinateBound M :=
  (by norm_num : (0 : ℝ) ≤ 3).trans (flowCoordinateBound_dominates hM).1

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureFirstBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Geometry

def riemannFirstBound (G d : ℝ) : ℝ :=
  2 * christoffelJetBound G d + 8 * (christoffelJetBound G d)^2
def curvatureNumeratorFirstBound (G d : ℝ) : ℝ := 4 * G * riemannFirstBound G d
def curvatureFirstBound (G d : ℝ) : ℝ :=
  curvatureNumeratorFirstBound G d / d +
    (curvatureNumeratorFirstBound G d + 16 * G^2 * (curvatureNumeratorFirstBound G d / d)) / d

theorem riemannFirstBound_nonneg {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d) :
    0 ≤ riemannFirstBound G d := by
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [riemannFirstBound] <;> positivity

theorem curvatureFirstBound_nonneg {G d : ℝ} (hG : 0 ≤ G) (hd : 0 < d) :
    0 ≤ curvatureFirstBound G d := by
  have hR := riemannFirstBound_nonneg hG hd
  dsimp [curvatureFirstBound, curvatureNumeratorFirstBound] <;> positivity

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_HeightEnergyJetBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def heightEnergyJetBound (G Z : ℝ) : ℝ := 16 * G^2 + 256 * G * Z^2
def darbouxGJetBound (G Z d c : ℝ) : ℝ :=
  LowQuotient.boundThroughThree
    (heightEnergyJetBound G Z + 8 * (hessianJetBound G Z d)^2) (c^2)

theorem heightEnergyJetBound_nonneg {G Z : ℝ} (hG : 0 ≤ G) : 0 ≤ heightEnergyJetBound G Z := by
  dsimp [heightEnergyJetBound] <;> positivity

theorem darbouxGJetBound_nonneg {G Z d c : ℝ} (hG : 0 ≤ G) (hc : 0 < c) :
    0 ≤ darbouxGJetBound G Z d c := by
  have hE := heightEnergyJetBound_nonneg (Z := Z) hG
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg
    (show 0 ≤ heightEnergyJetBound G Z + 8 * (hessianJetBound G Z d)^2 by positivity) (pow_pos hc 2)
  dsimp [darbouxGJetBound, LowQuotient.boundThroughThree]
  positivity

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_HeightPFirstBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

def heightQuotientJetBound (G Z d c : ℝ) : ℝ :=
  LowQuotient.boundThroughThree (hessianJetBound G Z d) c
def heightAlongDJetBound (G Z d c : ℝ) : ℝ :=
  christoffelJetBound G d + 16 * heightQuotientJetBound G Z d c * christoffelJetBound G d +
    64 * (heightQuotientJetBound G Z d c)^2 * christoffelJetBound G d
def heightEnergyFirstQuotientBound (G Z d c : ℝ) : ℝ :=
  LowQuotient.boundThroughThree (32 * G * Z + hessianJetBound G Z d) c
def heightPFirstBound (G Z d c : ℝ) : ℝ :=
  heightAlongDJetBound G Z d c + 2 * curvatureFirstBound G d *
    (heightEnergyFirstQuotientBound G Z d c + 8 * darbouxGJetBound G Z d c * christoffelJetBound G d)

theorem heightQuotientJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightQuotientJetBound G Z d c := by
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg (hessianJetBound_nonneg hG hZ hd) hc
  dsimp [heightQuotientJetBound, LowQuotient.boundThroughThree]
  positivity

theorem heightAlongDJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightAlongDJetBound G Z d c := by
  have hq := heightQuotientJetBound_nonneg hG hZ hd hc
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [heightAlongDJetBound] <;> positivity

theorem heightEnergyFirstQuotientBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightEnergyFirstQuotientBound G Z d c := by
  have hH := hessianJetBound_nonneg hG hZ hd
  obtain ⟨h0, h1, h2, h3⟩ := LowQuotient.bounds_nonneg (show 0 ≤ 32 * G * Z + hessianJetBound G Z d by positivity) hc
  dsimp [heightEnergyFirstQuotientBound, LowQuotient.boundThroughThree]
  positivity

theorem heightPFirstBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) : 0 ≤ heightPFirstBound G Z d c := by
  have hA := heightAlongDJetBound_nonneg hG hZ hd hc
  have hK := curvatureFirstBound_nonneg hG hd
  have hJ := heightEnergyFirstQuotientBound_nonneg hG hZ hd hc
  have hD := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hΓ := christoffelJetBound_nonneg hG hd
  dsimp [heightPFirstBound] <;> positivity

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_HeightCoefficientClosedBounds
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

def heightDriftErrorBound (G Z d c : ℝ) : ℝ :=
  heightEnergyJetBound G Z / c^2 *
    (2 * christoffelJetBound G d + hessianJetBound G Z d / c) +
    ((202 / 100 : ℝ) * (G + Z)^2) / c

theorem heightDriftErrorBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightDriftErrorBound G Z d c := by
  have hE := heightEnergyJetBound_nonneg (Z := Z) hG
  have hΓ := christoffelJetBound_nonneg hG hd
  have hH := hessianJetBound_nonneg hG hZ hd
  dsimp [heightDriftErrorBound] <;> positivity

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_HeightFlowUniformBounds
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

def flowRhoJetBound (M : ℝ) : ℝ :=
  1 / Real.exp (-2 * M) + flowCoordinateBound M / (Real.exp (-2 * M))^2
def heightG1JetBound (G Z d c : ℝ) : ℝ :=
  4 * (darbouxGJetBound G Z d c * (1 + flowCoordinateBound (heightQuotientJetBound G Z d c))) *
    (flowRhoJetBound (heightQuotientJetBound G Z d c))^2
def heightBJetBound (G Z d c : ℝ) (ell : ℕ) : ℝ :=
  (heightPFirstBound G Z d c + 2 * (ell : ℝ) * heightQuotientJetBound G Z d c) *
    (1 + flowCoordinateBound (heightQuotientJetBound G Z d c))
def heightG1Lower (G Z d c e0 : ℝ) : ℝ :=
  e0 / (1 + hessianJetBound G Z d)^2 *
    (1 / Real.exp (2 * heightQuotientJetBound G Z d c))^2
def heightRemainderBound (G Z d c e0 : ℝ) (ell : ℕ) : ℝ :=
  (heightDriftErrorBound G Z d c + darbouxGJetBound G Z d c) /
      ((e0 / (1 + hessianJetBound G Z d)^2) * (1 / Real.exp (2 * heightQuotientJetBound G Z d c))) +
    (2 * (ell : ℝ) + 1) *
      (flowCoordinateBound (heightQuotientJetBound G Z d c) /
        (Real.exp (-2 * heightQuotientJetBound G Z d c))^3) /
      (1 / Real.exp (2 * heightQuotientJetBound G Z d c))^2

theorem heightG1Lower_pos {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (he0 : 0 < e0) :
    0 < heightG1Lower G Z d c e0 := by
  have hH := hessianJetBound_nonneg hG hZ hd
  dsimp [heightG1Lower]
  positivity

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_HeightPrincipalBounds
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

def heightAJetBound (G Z d c : ℝ) : ℝ :=
  2 * heightG1JetBound G Z d c *
    (curvatureFirstBound G d * (1 + flowCoordinateBound (heightQuotientJetBound G Z d c)))

theorem heightG1JetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightG1JetBound G Z d c := by
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hDG := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  dsimp [heightG1JetBound] <;> positivity

theorem heightAJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) :
    0 ≤ heightAJetBound G Z d c := by
  have hG1 := heightG1JetBound_nonneg hG hZ hd hc
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hK := curvatureFirstBound_nonneg hG hd
  dsimp [heightAJetBound] <;> positivity

theorem heightBJetBound_nonneg {G Z d c : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (ell : ℕ) :
    0 ≤ heightBJetBound G Z d c ell := by
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hP := heightPFirstBound_nonneg hG hZ hd hc
  dsimp [heightBJetBound] <;> positivity

theorem heightRemainderBound_nonneg {G Z d c e0 : ℝ}
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c) (he0 : 0 < e0) (ell : ℕ) :
    0 ≤ heightRemainderBound G Z d c e0 ell := by
  have hQ := heightQuotientJetBound_nonneg hG hZ hd hc
  have hF := flowCoordinateBound_nonneg hQ
  have hDE := heightDriftErrorBound_nonneg hG hZ hd hc
  have hDG := darbouxGJetBound_nonneg (Z := Z) (d := d) hG hc
  have hH := hessianJetBound_nonneg hG hZ hd
  dsimp [heightRemainderBound] <;> positivity

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_HeightCapLowData
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

def heightCapCurvatureBound (G Z d c : ℝ) : ℝ :=
  curvatureFirstBound G d*(1+flowCoordinateBound (heightQuotientJetBound G Z d c))

def heightCapCValueBound (G Z d c e0 : ℝ) (ell : ℕ) : ℝ :=
  ((ell : ℝ)+1)*heightAJetBound G Z d c +
    heightAJetBound G Z d c*heightRemainderBound G Z d c e0 ell

def heightCapCoefficientBound (G Z d c e0 : ℝ) (ell : ℕ) : ℝ :=
  heightAJetBound G Z d c + 2*heightBJetBound G Z d c ell + heightCapCValueBound G Z d c e0 ell

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_HeightNumericParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

def HeightNumericData (G Z d c e0 kappa : ℝ) : Prop :=
  0 ≤ G ∧ 0 ≤ Z ∧ 0 < d ∧ 0 < c ∧ 0 < e0 ∧ 0 < kappa

def HeightDirectedBudgets (G Z d c e0 kappa : ℝ) (ell : ℕ) (v : ℝ × ℝ × ℝ) : Prop :=
  let epsilon := v.1
  let lambda := v.2.1
  let c1 := v.2.2
  let rhoMax := 1/Real.exp (-2*heightQuotientJetBound G Z d c)
  let cG := heightG1Lower G Z d c e0
  let MG := heightG1JetBound G Z d c
  let MB := heightBJetBound G Z d c ell
  let Mr := heightRemainderBound G Z d c e0 ell
  let MA := heightAJetBound G Z d c
  0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < lambda ∧ 0 < c1 ∧
  epsilon*2*((1 : ℝ)/100) ≤ ((ell : ℝ)+1/2)/rhoMax ∧
  2*(2*MB+epsilon+epsilon*2*MB) ≤ lambda ∧
  (2*MB+1+2*MB)/2+Mr ≤ lambda/8 ∧
  4*(2*((ell : ℝ)*MA+MA*Mr+MA*(2*MB)+1))^2*epsilon^2*MA ≤ 1/8 ∧
  (4*(2*((ell : ℝ)*MA+MA*Mr+MA*(2*MB)+1))^2*epsilon^2)/lambda ≤
    modelCoercivityMargin cG kappa rhoMax epsilon ell/8 ∧
  directedPrincipalBound ell epsilon 2 MA MA+modelCoercivityMargin cG kappa rhoMax epsilon ell/2 ≤
    lambda*(cG*modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell)/4 ∧
  c1*2 ≤ modelPrincipalRadius cG kappa rhoMax epsilon 2 MG ell ∧
  MG*c1*(lambda*2+8) ≤ modelCoercivityMargin cG kappa rhoMax epsilon ell/6

theorem exists_heightDirectedBudgets {G Z d c e0 kappa : ℝ}
    (h : HeightNumericData G Z d c e0 kappa) (ell : ℕ) :
    ∃ v : ℝ × ℝ × ℝ, HeightDirectedBudgets G Z d c e0 kappa ell v := by
  obtain ⟨hG,hZ,hd,hc,he0,hk⟩ := h
  have hcG := heightG1Lower_pos (c := c) hG hZ hd he0
  have hrho : 0 < 1/Real.exp (-2*heightQuotientJetBound G Z d c) := by positivity
  have hMG := heightG1JetBound_nonneg hG hZ hd hc
  have hMB := heightBJetBound_nonneg hG hZ hd hc ell
  have hMr := heightRemainderBound_nonneg hG hZ hd hc he0 ell
  have hMA := heightAJetBound_nonneg hG hZ hd hc
  obtain ⟨epsilon,lambda,c1,hbudget⟩ :=
    exists_directed_parameters ell hk hcG hrho hMG (show 0 ≤ 2*heightBJetBound G Z d c ell by positivity)
      hMB hMr hMA hMA hMA hMG (by norm_num : (0 : ℝ) ≤ 2)
  exact ⟨(epsilon,lambda,c1),hbudget⟩

def heightDirectedNumbers (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ × ℝ × ℝ := by
  classical
  exact if h : HeightNumericData G Z d c e0 kappa then Classical.choose (exists_heightDirectedBudgets h ell)
    else (1,1,1)

def heightDirectedEpsilon (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  (heightDirectedNumbers G Z d c e0 kappa ell).1
def heightDirectedLambda (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  (heightDirectedNumbers G Z d c e0 kappa ell).2.1
def heightDirectedSlope (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  (heightDirectedNumbers G Z d c e0 kappa ell).2.2
def heightDirectedCoercivity (G Z d c e0 kappa : ℝ) (ell : ℕ) : ℝ :=
  min (heightDirectedLambda G Z d c e0 kappa ell/8)
    (modelCoercivityMargin (heightG1Lower G Z d c e0) kappa
      (1/Real.exp (-2*heightQuotientJetBound G Z d c))
      (heightDirectedEpsilon G Z d c e0 kappa ell) ell/4)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_RectangleSobolevOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval

namespace SmoothLocal.Sobolev

theorem abs_two_mul_le_squares (a b : ℝ) : |2 * a * b| ≤ a^2 + b^2 := by
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]

end SmoothLocal.Sobolev

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_RectangleSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry SmoothLocal.Weighted

variable {tl tr sb st : ℝ}

theorem rectangle_vertical_integral_intervalIntegrable
    {F : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    IntervalIntegrable (fun t => ∫ s in sb..st, F (boxPoint t s)) volume tl tr := by
  have hi : Integrable (fun p : ℝ × ℝ => F (boxPoint p.1 p.2))
      ((volume.restrict (Ioc tl tr)).prod (volume.restrict (Ioc sb st))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact rectangle_area_integrable hF
  have hj := hi.integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  simpa only [intervalIntegral.integral_of_le hs, IntegrableOn] using hj

end SmoothLocal.Sobolev

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_RegionSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem boxPoint_eta (p : Coord) : boxPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [boxPoint]

end SmoothLocal.Sobolev

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapAreaFormula
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

theorem capRectangle_isCompact (tl tr sb st : ℝ) : IsCompact (closedRectangle tl tr sb st) := by
  have he : closedRectangle tl tr sb st =
      (fun q : ℝ × ℝ => boxPoint q.1 q.2) '' (Icc tl tr ×ˢ Icc sb st) := by
    ext p
    constructor
    · intro hp
      exact ⟨(p 0,p 1),⟨hp.1,hp.2⟩,boxPoint_eta p⟩
    · rintro ⟨q,hq,rfl⟩
      exact boxPoint_mem hq.1 hq.2
  rw [he]
  exact (isCompact_Icc.prod isCompact_Icc).image (by unfold boxPoint; fun_prop)

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

def heightCapIntegralFactors (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) : ℝ × ℝ :=
  let lambda := heightDirectedLambda G Z d c e0 kappa ell
  let c1 := heightDirectedSlope G Z d c e0 kappa ell
  let c2 := heightDirectedCoercivity G Z d c e0 kappa ell
  let M := heightCapCoefficientBound G Z d c e0 ell
  let MK := heightCapCurvatureBound G Z d c
  let glow := heightG1Lower G Z d c e0
  let MI := 2*heightBJetBound G Z d c ell
  let D := capDistanceBound bottom b
  let COverlap := capOverlapEnergyCost L R bottom b kappa c1 c2 glow M lambda MI
  let HElliptic := capEllipticRatioBudget L R bottom b kappa c1 glow MK M
  let S := 2/(c2*capInteriorWeightFloor top b lambda MI)
  (S*((5/(2*c2))*(D^8*Real.exp (lambda*2+MI))+COverlap*D^6),
    S*(COverlap*(D^6+HElliptic)))

def heightPhysicalCapConstant (G Z d c e0 kappa : ℝ) (ell : ℕ)
    (L R bottom top b : ℝ) : ℝ :=
  let H := Real.exp (2*heightQuotientJetBound G Z d c)
  let A := heightCapIntegralFactors G Z d c e0 kappa ell L R bottom top b
  H*(2+3*H^2)*H*(|A.1|+|A.2|+1)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_AllOrderPhysicalCap
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

theorem cap_closed_image_properties {Y : ℝ → ℝ → ℝ}
    (hYs : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2))
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1:ℝ)/50)
    {tl tr sb st : ℝ} (hbox : closedRectangle tl tr sb st ⊆ capChartDomain) :
    IsCompact (capChart Y '' closedRectangle tl tr sb st) ∧
    MeasurableSet (capChart Y '' closedRectangle tl tr sb st) ∧
    volume (capChart Y '' closedRectangle tl tr sb st) < ⊤ ∧
    capChart Y '' closedRectangle tl tr sb st ⊆ modelOpenSquare := by
  have hc : IsCompact (capChart Y '' closedRectangle tl tr sb st) :=
    (capRectangle_isCompact _ _ _ _).image_of_continuousOn
      ((capChart_contDiffOn hYs).continuousOn.mono hbox)
  refine ⟨hc,hc.measurableSet,hc.measure_lt_top,?_⟩
  rintro _ ⟨p,hp,rfl⟩
  exact capChart_mem_modelOpenSquare (hbox hp) (hdisp p (hbox hp))

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_FiniteProductL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace SmoothLocal.Analytic

variable {ι α : Type*} [DecidableEq ι]

theorem finite_product_one_factor_bound (s : Finset ι) (f : ι → α → ℝ)
    {j : ι} (hj : j ∈ s) {B : ℝ} (hB : 0 ≤ B) (x : α)
    (hb : ∀ i ∈ s.erase j, ‖f i x‖ ≤ B) :
    ‖∏ i ∈ s, f i x‖ ≤ B ^ (s.erase j).card * ‖f j x‖ := by
  have hprod : ‖∏ i ∈ s.erase j, f i x‖ ≤ B ^ (s.erase j).card := by
    calc
      _ ≤ ∏ i ∈ s.erase j, ‖f i x‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ _i ∈ s.erase j, B := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hb
      _ = _ := Finset.prod_const B
  rw [← Finset.prod_erase_mul s (fun i => f i x) hj, norm_mul]
  exact mul_le_mul hprod le_rfl (norm_nonneg _) (pow_nonneg hB _)

variable [MeasurableSpace α] {μ : Measure α} {U : Set α}

theorem finite_product_eLpNorm_two (s : Finset ι) (f : ι → α → ℝ)
    {j : ι} (hj : j ∈ s) {B : ℝ} (hB : 0 ≤ B) (hU : MeasurableSet U)
    (hb : ∀ i ∈ s.erase j, ∀ x ∈ U, ‖f i x‖ ≤ B) :
    eLpNorm' (fun x => ∏ i ∈ s, f i x) (2 : ℝ) (μ.restrict U) ≤
      ‖B ^ (s.erase j).card‖ₑ * eLpNorm' (f j) (2 : ℝ) (μ.restrict U) := by
  have hdom : ∀ᵐ x ∂(μ.restrict U),
      ‖∏ i ∈ s, f i x‖ ≤ ‖B ^ (s.erase j).card * f j x‖ := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg hB (s.erase j).card)]
    exact finite_product_one_factor_bound s f hj hB x (fun i hi => hb i hi x hx)
  calc
    _ ≤ eLpNorm' (fun x => B ^ (s.erase j).card * f j x) (2 : ℝ) (μ.restrict U) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := eLpNorm'_const_smul (𝕜 := ℝ) (F := ℝ) (f := f j)
      (B ^ (s.erase j).card) (by norm_num)

theorem finite_product_eLpNorm_two_of_aestronglyMeasurable
    (indices : Finset ι) (factors : ι → α → ℝ) {chosen : ι} (hchosen : chosen ∈ indices)
    {bound : ℝ} (hbound : 0 ≤ bound) (hU : MeasurableSet U)
    (hb : ∀ index ∈ indices.erase chosen, ∀ point ∈ U, ‖factors index point‖ ≤ bound)
    (hmeas : AEStronglyMeasurable
      (fun point => ∏ index ∈ indices, factors index point) (μ.restrict U)) :
    eLpNorm (fun point => ∏ index ∈ indices, factors index point) 2 (μ.restrict U) ≤
      ‖bound ^ (indices.erase chosen).card‖ₑ * eLpNorm (factors chosen) 2 (μ.restrict U) := by
  have hfactor : eLpNorm' (factors chosen) (2 : ℝ) (μ.restrict U) ≤
      eLpNorm (factors chosen) 2 (μ.restrict U) := by
    by_cases hfactorMeas : AEStronglyMeasurable (factors chosen) (μ.restrict U)
    · rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
      norm_num
    · rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)]
      norm_num
  calc
    _ = eLpNorm' (fun point => ∏ index ∈ indices, factors index point)
        (2 : ℝ) (μ.restrict U) := by
      simpa only [ENNReal.toReal_ofNat] using
        (eLpNorm_eq_eLpNorm' (p := 2) (by norm_num) (by norm_num))
    _ ≤ ‖bound ^ (indices.erase chosen).card‖ₑ *
        eLpNorm' (factors chosen) (2 : ℝ) (μ.restrict U) :=
      finite_product_eLpNorm_two indices factors hchosen hbound hU hb
    _ ≤ _ := mul_le_mul_right hfactor _

end SmoothLocal.Analytic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_FiniteSumL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal

namespace SmoothLocal.Analytic
variable {ι α : Type*} [MeasurableSpace α] {μ : Measure α} {U : Set α}

theorem finite_product_bounded_eLpNorm_two (s : Finset ι) (f : ι → α → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hU : MeasurableSet U)
    (hb : ∀ i ∈ s, ∀ x ∈ U, ‖f i x‖ ≤ B) :
    eLpNorm' (fun x => ∏ i ∈ s, f i x) (2 : ℝ) (μ.restrict U) ≤
      ‖B ^ s.card‖ₑ * (μ U) ^ (1 / (2 : ℝ)) := by
  have hdom : ∀ᵐ x ∂(μ.restrict U), ‖∏ i ∈ s, f i x‖ ≤ ‖B ^ s.card‖ := by
    filter_upwards [ae_restrict_mem hU] with x hx
    rw [Real.norm_of_nonneg (pow_nonneg hB s.card)]
    calc
      _ ≤ ∏ i ∈ s, ‖f i x‖ := Finset.norm_prod_le s _
      _ ≤ ∏ _i ∈ s, B :=
        Finset.prod_le_prod (fun index _ => norm_nonneg (f index x))
          (fun index hindex => hb index hindex x hx)
      _ = _ := Finset.prod_const B
  calc
    _ ≤ eLpNorm' (fun _ : α => B ^ s.card) (2 : ℝ) (μ.restrict U) :=
      eLpNorm'_mono_ae (by norm_num) hdom
    _ = _ := by
      rw [eLpNorm'_const (B ^ s.card) (by norm_num), Measure.restrict_apply_univ]

theorem finite_product_bounded_eLpNorm_two_of_aestronglyMeasurable
    (s : Finset ι) (f : ι → α → ℝ) {B : ℝ} (hB : 0 ≤ B) (hU : MeasurableSet U)
    (hb : ∀ i ∈ s, ∀ x ∈ U, ‖f i x‖ ≤ B)
    (hm : AEStronglyMeasurable (fun x => ∏ i ∈ s, f i x) (μ.restrict U)) :
    eLpNorm (fun x => ∏ i ∈ s, f i x) 2 (μ.restrict U) ≤
      ‖B ^ s.card‖ₑ * (μ U) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  exact finite_product_bounded_eLpNorm_two s f hB hU hb

theorem finite_sum_eLpNorm_two (s : Finset ι) (f : ι → α → ℝ)
    (C : ι → ℝ≥0∞)
    (_hm : ∀ i ∈ s, AEStronglyMeasurable (f i) (μ.restrict U))
    (hb : ∀ i ∈ s, eLpNorm (f i) 2 (μ.restrict U) ≤ C i) :
    eLpNorm (fun x => ∑ i ∈ s, f i x) 2 (μ.restrict U) ≤ ∑ i ∈ s, C i := by
  have hsum := eLpNorm_sum_le (hfs := fun _ _ => by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (f := f) (s := s) (μ := μ.restrict U)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have he : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext x
    simp only [Finset.sum_apply]
  rw [he]
  exact hsum.trans (Finset.sum_le_sum hb)

end SmoothLocal.Analytic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowImageFirstBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem cap_flow_seed_gap {M s0 s1 t : ℝ} (hM : 0 ≤ M)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hs0 : s0 ∈ Ioo (-2 : ℝ) 2) (hs1 : s1 ∈ Ioo (-2 : ℝ) 2)
    (ht : t ∈ Ioo (-2 : ℝ) 2) (hss : s0 ≤ s1) :
    Real.exp (-2 * M) * (s1 - s0) ≤ Y s1 t - Y s0 t := by
  have hd (s : ℝ) (hs : s ∈ Ioo (-2 : ℝ) 2) :
      DifferentiableAt ℝ (fun r => Y r t) s :=
    (cap_flow_hasDerivAt_initial hq hU hSU hY hrange hstart hode hs ht).differentiableAt
  have hc : ContinuousOn (fun r => Y r t) (Ioo (-2 : ℝ) 2) :=
    fun s hs => (hd s hs).continuousAt.continuousWithinAt
  have hdi : DifferentiableOn ℝ (fun r => Y r t) (interior (Ioo (-2 : ℝ) 2)) := by
    intro s hs
    exact (hd s (interior_subset hs)).differentiableWithinAt
  have hbound : ∀ s ∈ interior (Ioo (-2 : ℝ) 2),
      Real.exp (-2 * M) ≤ deriv (fun r => Y r t) s := by
    intro s hs
    exact (cap_flow_initial_deriv_bounds hq hU hSU hY hrange hstart hode hM hq1
      (interior_subset hs) ht).1
  exact (convex_Ioo (-2 : ℝ) 2).mul_sub_le_image_sub_of_le_deriv hc hdi hbound
    s0 hs0 s1 hs1 hss

theorem cap_flow_time_lipschitz
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    {s t0 t1 : ℝ} (hs : s ∈ Ioo (-2 : ℝ) 2)
    (ht0 : t0 ∈ Ioo (-2 : ℝ) 2) (ht1 : t1 ∈ Ioo (-2 : ℝ) 2) :
    |Y s t1 - Y s t0| ≤ ((1 : ℝ) / 100) * |t1 - t0| := by
  have hd (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) : DifferentiableAt ℝ (Y s) t :=
    (cap_flow_time_hasDerivAt hq hU hSU hY hrange hstart hode hs ht).differentiableAt
  have hb (t : ℝ) (ht : t ∈ Ioo (-2 : ℝ) 2) : ‖deriv (Y s) t‖ ≤ (1 : ℝ) / 100 := by
    simpa only [Real.norm_eq_abs, timeFlowDerivative] using
      cap_flow_time_bound hq hU hSU hY hrange hstart hode hq0 hs ht
  simpa only [Real.norm_eq_abs] using
    (convex_Ioo (-2 : ℝ) 2).norm_image_sub_le_of_norm_deriv_le hd hb ht0 ht1

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowImageMargin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

def openCoordinateRectangle (tl tr sb st : ℝ) : Set Coord :=
  {p | p 0 ∈ Ioo tl tr ∧ p 1 ∈ Ioo sb st}

def flowInteriorRadius (M dt ds : ℝ) : ℝ :=
  min (dt / 2) (((50 : ℝ) / 101) * Real.exp (-2 * M) * ds)

theorem flowInteriorRadius_pos (M : ℝ) {dt ds : ℝ} (ht : 0 < dt) (hs : 0 < ds) :
    0 < flowInteriorRadius M dt ds := by
  apply lt_min
  · exact half_pos ht
  · exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hs

theorem flowInteriorRadius_lt_time (M : ℝ) {dt ds : ℝ} (ht : 0 < dt) :
    flowInteriorRadius M dt ds < dt := by
  have h := min_le_left (dt / 2) (((50 : ℝ) / 101) * Real.exp (-2 * M) * ds)
  change flowInteriorRadius M dt ds ≤ dt / 2 at h
  linarith

theorem flowInteriorRadius_vertical_margin (M : ℝ) {dt ds : ℝ} (hs : 0 < ds) :
    ((101 : ℝ) / 100) * flowInteriorRadius M dt ds < Real.exp (-2 * M) * ds := by
  have h := min_le_right (dt / 2) (((50 : ℝ) / 101) * Real.exp (-2 * M) * ds)
  change flowInteriorRadius M dt ds ≤ ((50 : ℝ) / 101) * Real.exp (-2 * M) * ds at h
  have hp := mul_pos (Real.exp_pos (-2 * M)) hs
  nlinarith

variable {q : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
include hq hU hSU hY hrange hstart hode

theorem actual_flow_ordinary_rectangle_inclusion
    {M tl tr sb st dt ds t0 s0 : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds)
    (ht0 : t0 ∈ Icc (tl + dt) (tr - dt))
    (hs0 : s0 ∈ Icc (sb + ds) (st - ds)) :
    closedRectangle (t0 - flowInteriorRadius M dt ds) (t0 + flowInteriorRadius M dt ds)
      (Y s0 t0 - flowInteriorRadius M dt ds) (Y s0 t0 + flowInteriorRadius M dt ds) ⊆
      capChart Y '' openCoordinateRectangle tl tr sb st := by
  intro p hp
  let r := flowInteriorRadius M dt ds
  have hr : 0 < r := flowInteriorRadius_pos M hdt hds
  have hrt : r < dt := flowInteriorRadius_lt_time M hdt
  have hrs : ((101 : ℝ) / 100) * r < Real.exp (-2 * M) * ds :=
    flowInteriorRadius_vertical_margin M hds
  have hpx : p 0 ∈ Icc (t0 - r) (t0 + r) := hp.1
  have hpy : p 1 ∈ Icc (Y s0 t0 - r) (Y s0 t0 + r) := hp.2
  have htime : p 0 ∈ Ioo tl tr := by constructor <;> linarith [ht0.1, ht0.2, hpx.1, hpx.2]
  have htimeGlobal : p 0 ∈ Ioo (-2 : ℝ) 2 := ⟨htl.trans htime.1, htime.2.trans htr⟩
  have ht0Global : t0 ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [ht0.1, ht0.2]
  have hs0Global : s0 ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [hs0.1, hs0.2]
  have hsbGlobal : sb ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [hs0.1, hs0.2]
  have hstGlobal : st ∈ Ioo (-2 : ℝ) 2 := by constructor <;> linarith [hs0.1, hs0.2]
  have hsb0 : sb ≤ s0 := by linarith [hs0.1]
  have hs0t : s0 ≤ st := by linarith [hs0.2]
  have hlow := cap_flow_seed_gap hq hU hSU hY hrange hstart hode hM hq1
    hsbGlobal hs0Global htimeGlobal hsb0
  have hupp := cap_flow_seed_gap hq hU hSU hY hrange hstart hode hM hq1
    hs0Global hstGlobal htimeGlobal hs0t
  have hgap0 : Real.exp (-2 * M) * ds ≤ Real.exp (-2 * M) * (s0 - sb) :=
    mul_le_mul_of_nonneg_left (by linarith [hs0.1]) (Real.exp_pos _).le
  have hgap1 : Real.exp (-2 * M) * ds ≤ Real.exp (-2 * M) * (st - s0) :=
    mul_le_mul_of_nonneg_left (by linarith [hs0.2]) (Real.exp_pos _).le
  have hxdist : |p 0 - t0| ≤ r := abs_le.mpr ⟨by linarith [hpx.1], by linarith [hpx.2]⟩
  have hmove : |Y s0 (p 0) - Y s0 t0| ≤ ((1 : ℝ) / 100) * r :=
    (cap_flow_time_lipschitz hq hU hSU hY hrange hstart hode hq0
      hs0Global ht0Global htimeGlobal).trans
      (mul_le_mul_of_nonneg_left hxdist (by norm_num))
  have hlo : Y sb (p 0) < p 1 := by
    have hm := (abs_le.mp hmove).2
    nlinarith [hlow, hgap0, hpy.1, hrs]
  have hhi : p 1 < Y st (p 0) := by
    have hm := (abs_le.mp hmove).1
    nlinarith [hupp, hgap1, hpy.2, hrs]
  have hsb_st : sb ≤ st := hsb0.trans hs0t
  have hseedCont : ContinuousOn (fun s : ℝ => (s, p 0)) (Icc sb st) := by fun_prop
  have hseedMap : MapsTo (fun s : ℝ => (s, p 0)) (Icc sb st)
      (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2) := by
    intro s hs
    exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩,
      ⟨htimeGlobal.1.le, htimeGlobal.2.le⟩⟩
  have hcont : ContinuousOn (fun s => Y s (p 0)) (Icc sb st) := by
    convert hY.comp hseedCont hseedMap using 1; rfl
  obtain ⟨s, hs, hse⟩ := intermediate_value_Icc hsb_st hcont ⟨hlo.le, hhi.le⟩
  have hsStrict : s ∈ Ioo sb st := by
    constructor
    · by_contra hnot
      have he : s = sb := le_antisymm (le_of_not_gt hnot) hs.1
      subst s
      linarith
    · by_contra hnot
      have he : s = st := le_antisymm hs.2 (le_of_not_gt hnot)
      subst s
      linarith
  refine ⟨boxPoint (p 0) s, ?_, ?_⟩
  · simpa [openCoordinateRectangle, boxPoint] using And.intro htime hsStrict
  · ext i
    fin_cases i <;> simp [capChart, capFlowHeight, boxPoint, coordinatePoint, hse]

theorem actual_flow_uniform_image_margin
    {M tl tr sb st dt ds : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds) :
    0 < flowInteriorRadius M dt ds ∧
      ∀ p ∈ capChart Y '' closedRectangle (tl + dt) (tr - dt) (sb + ds) (st - ds),
        closedRectangle (p 0 - flowInteriorRadius M dt ds) (p 0 + flowInteriorRadius M dt ds)
          (p 1 - flowInteriorRadius M dt ds) (p 1 + flowInteriorRadius M dt ds) ⊆
          capChart Y '' openCoordinateRectangle tl tr sb st := by
  refine ⟨flowInteriorRadius_pos M hdt hds, ?_⟩
  rintro p ⟨a, ha, rfl⟩
  simpa [capChart, capFlowHeight, coordinatePoint] using
    actual_flow_ordinary_rectangle_inclusion hq hU hSU hY hrange hstart hode
      hM hq0 hq1 htl htr hsb hst hdt hds ha.1 ha.2

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowSobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev

theorem openCoordinateRectangle_subset_closed (tl tr sb st : ℝ) :
    openCoordinateRectangle tl tr sb st ⊆ closedRectangle tl tr sb st := by
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩

variable {q f : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)

include hSU hrange

theorem actual_closed_flow_rectangle_subset_domain
    {tl tr sb st : ℝ} (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2) :
    capChart Y '' closedRectangle tl tr sb st ⊆ U := by
  rintro p ⟨a, ha, rfl⟩
  apply hSU
  apply coordinatePoint_mem_modelSquare
  · exact ⟨by linarith [ha.1.1], by linarith [ha.1.2]⟩
  · exact hrange (a 1) ⟨by linarith [ha.2.1], by linarith [ha.2.2]⟩
      (a 0) ⟨by linarith [ha.1.1], by linarith [ha.1.2]⟩

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapL2Basics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

theorem integral_sq_eq_eLpNorm_toReal_sq {f : Coord → ℝ} {μ : Measure Coord}
    (hf : MemLp f 2 μ) :
    (∫ p, f p ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  calc
    (∫ p, f p ^ 2 ∂μ) = ∫ p, ‖hf.toLp f p‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with p hp
      simp only [hp, Real.norm_eq_abs, sq_abs]
    _ = ∫ p, inner ℝ (hf.toLp f p) (hf.toLp f p) ∂μ := by
      simp only [real_inner_self_eq_norm_sq]
    _ = inner ℝ (hf.toLp f) (hf.toLp f) := rfl
    _ = ‖hf.toLp f‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = (eLpNorm f 2 μ).toReal ^ 2 := by
      rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]

theorem integral_sq_le_of_eLpNorm_two_le {f : Coord → ℝ} {μ : Measure Coord}
    (hf : MemLp f 2 μ) {H : ℝ≥0} (hH : eLpNorm f 2 μ ≤ (H : ℝ≥0∞)) :
    (∫ p, f p ^ 2 ∂μ) ≤ (H : ℝ)^2 := by
  rw [integral_sq_eq_eLpNorm_toReal_sq hf]
  have h := ENNReal.toReal_mono (by simp : (H : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) hH
  change (eLpNorm f 2 μ).toReal ≤ (H : ℝ) at h
  exact (sq_le_sq₀ ENNReal.toReal_nonneg H.2).mpr h

theorem eLpNorm_two_le_of_integral_sq_le {f : Coord → ℝ} {μ : Measure Coord}
    (hf : MemLp f 2 μ) {H : ℝ≥0} (hH : (∫ p, f p ^ 2 ∂μ) ≤ (H : ℝ)^2) :
    eLpNorm f 2 μ ≤ (H : ℝ≥0∞) := by
  apply (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top (by simp)).mp
  rw [integral_sq_eq_eLpNorm_toReal_sq hf] at hH
  change (eLpNorm f 2 μ).toReal ≤ (H : ℝ)
  exact (sq_le_sq₀ ENNReal.toReal_nonneg H.2).mp hH

end SmoothLocal.Analytic

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev
open SmoothLocal.HighEquation

theorem closedRectangle_subset_capChartDomain
    {tl tr sb st : ℝ} (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2) :
    closedRectangle tl tr sb st ⊆ capChartDomain := by
  intro p hp
  exact ⟨⟨htl.trans_le hp.1.1, hp.1.2.trans_lt htr⟩,
    ⟨hsb.trans_le hp.2.1, hp.2.2.trans_lt hst⟩⟩

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_NestedCapRectangles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.ODE

structure LowerCapRectangle (bStar : ℝ) where
  left : ℝ
  right : ℝ
  bottom : ℝ
  top : ℝ
  left_gt : -2 < left
  right_lt : right < 2
  bottom_gt : -2 < bottom
  horizontal : left ≤ right
  vertical : bottom ≤ top
  top_lt : top < bStar
  ceiling_le : bStar ≤ 0

namespace LowerCapRectangle

variable {bStar : ℝ}

def region (r : LowerCapRectangle bStar) : Set Coord := closedRectangle r.left r.right r.bottom r.top

def image (r : LowerCapRectangle bStar) (Y : ℝ → ℝ → ℝ) : Set Coord := capChart Y '' r.region

theorem region_subset_domain (r : LowerCapRectangle bStar) : r.region ⊆ capChartDomain :=
  closedRectangle_subset_capChartDomain r.left_gt r.right_lt r.bottom_gt (by linarith [r.top_lt,r.ceiling_le])

def energyOuter (r : LowerCapRectangle bStar) : LowerCapRectangle bStar where
  left := capOuterLeft r.left
  right := capOuterRight r.right
  bottom := capOuterBottom r.bottom
  top := (r.top+bStar) / 2
  left_gt := (capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt).1
  right_lt := (capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt).2.2.2.2.2.1
  bottom_gt := (capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt).2.2.2.2.2.2.1
  horizontal := by
    obtain ⟨_,_,_,_,_,_,_,_,_,hL,hR⟩ := capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt
    linarith [r.horizontal]
  vertical := by
    obtain ⟨_,_,_,_,_,_,_,hB0,hB1,_,_⟩ := capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt
    linarith [r.vertical,r.top_lt]
  top_lt := by linarith [r.top_lt]
  ceiling_le := r.ceiling_le

def margin (r : LowerCapRectangle bStar) : ℝ :=
  min ((r.left+2)/2) (min ((2-r.right)/2) (min ((r.bottom+2)/2) ((bStar-r.top)/2)))

theorem margin_pos (r : LowerCapRectangle bStar) : 0 < r.margin := by
  unfold margin
  apply lt_min
  · linarith [r.left_gt]
  · apply lt_min
    · linarith [r.right_lt]
    · apply lt_min <;> linarith [r.bottom_gt,r.top_lt]

theorem margin_bounds (r : LowerCapRectangle bStar) :
    r.margin ≤ (r.left+2)/2 ∧ r.margin ≤ (2-r.right)/2 ∧
    r.margin ≤ (r.bottom+2)/2 ∧ r.margin ≤ (bStar-r.top)/2 := by
  unfold margin
  refine ⟨min_le_left _ _, ?_, ?_, ?_⟩
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)

def expand (r : LowerCapRectangle bStar) : LowerCapRectangle bStar where
  left := r.left-r.margin
  right := r.right+r.margin
  bottom := r.bottom-r.margin
  top := r.top+r.margin
  left_gt := by linarith [r.margin_bounds.1,r.left_gt]
  right_lt := by linarith [r.margin_bounds.2.1,r.right_lt]
  bottom_gt := by linarith [r.margin_bounds.2.2.1,r.bottom_gt]
  horizontal := by linarith [r.horizontal,r.margin_pos]
  vertical := by linarith [r.vertical,r.margin_pos]
  top_lt := by linarith [r.margin_bounds.2.2.2,r.top_lt]
  ceiling_le := r.ceiling_le

theorem expand_shrink_region (r : LowerCapRectangle bStar) :
    closedRectangle (r.expand.left+r.margin) (r.expand.right-r.margin)
      (r.expand.bottom+r.margin) (r.expand.top-r.margin) = r.region := by
  dsimp only [expand, region]
  congr 1 <;> ring

end LowerCapRectangle

end SmoothLocal.Flow

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

structure CapInductionHeight (g : MetricField) (U : Set Coord) (Z c e0 : ℝ)
    (z : Coord → ℝ) : Prop where
  smooth : ContDiffOn ℝ ∞ z U
  lowJet : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z
  denominator : ∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|
  energy : ∀ p ∈ modelSquare, e0 ≤ heightEnergy g z p
  quotient : ∀ p ∈ modelSquare, |hessianQuotient g z p| ≤ (1 : ℝ)/100
  darboux : ∀ p ∈ modelSquare,
    (covHessian g z p).det = gaussianCurvature g p*heightEnergy g z p

def lowerCapConstant (G Z d c e0 kappa : ℝ) (ell : ℕ) (r : LowerCapRectangle bStar) : ℝ :=
  heightPhysicalCapConstant G Z d c e0 kappa ell r.left r.right r.bottom r.top ((r.top+bStar)/2)

structure CapInductionFlow (g : MetricField) (U : Set Coord) (G Z d c e0 kappa : ℝ)
    (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord) : Prop where
  domainOpen : IsOpen W
  squareSubset : modelSquare ⊆ W
  domainSubset : W ⊆ U
  quotientSmooth : ContDiffOn ℝ ∞ (hessianQuotient g z) W
  quotientBound : CoordinateBound (hessianQuotient g z) modelSquare 3 (heightQuotientJetBound G Z d c)
  continuous : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2)
  jointSmooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Y p.2 p.1) (pairRectangle 2 (-2) 2)
  start : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s
  ode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
    HasDerivWithinAt (Y s) (-hessianQuotient g z (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t
  range : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3
  displacement : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50
  physicalEstimate : ∀ m : ℕ, ∀ {bStar : ℝ}, ∀ r : LowerCapRectangle bStar,
    (∫ p in r.image Y, (coordPartial 0 (verticalJet z (m+3)) p)^2+(verticalJet z (m+4) p)^2) ≤
      lowerCapConstant G Z d c e0 kappa (m+3) r *
        ((∫ p in r.energyOuter.image Y, (actualHighRemainder g z m p)^2)+
          (∫ p in r.energyOuter.image Y, (verticalJet z (m+3) p)^2))

theorem CapInductionFlow.image_properties
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W) (r : LowerCapRectangle bStar) :
    IsCompact (r.image Y) ∧ MeasurableSet (r.image Y) ∧ volume (r.image Y) < ⊤ ∧
      r.image Y ⊆ modelOpenSquare :=
  cap_closed_image_properties hf.jointSmooth hf.displacement r.region_subset_domain

theorem CapInductionFlow.image_subset_square
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hf : CapInductionFlow g U G Z d c e0 kappa z Y W) (r : LowerCapRectangle bStar) :
    r.image Y ⊆ modelSquare := (hf.image_properties r).2.2.2.trans modelOpenSquare_subset

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_AffinePullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def matrixContinuousLinear (R : Matrix (Fin 2) (Fin 2) ℝ) : Coord →L[ℝ] Coord :=
  LinearMap.toContinuousLinearMap R.mulVecLin

@[simp] theorem matrixContinuousLinear_apply (R : Matrix (Fin 2) (Fin 2) ℝ) (v : Coord) :
    matrixContinuousLinear R v = R *ᵥ v := rfl

def affineCoordinates (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord) : Coord :=
  b + R *ᵥ q

def affinePullbackMetric (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : MetricField := fun q =>
  Rᵀ * g (affineCoordinates b R q) * R

@[simp] theorem affineCoordinates_zero (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    affineCoordinates b R 0 = b := by simp [affineCoordinates]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_CoordinateSwap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def swapCoordinateIndex (i : Fin 2) : Fin 2 := ![1, 0] i

def coordinateSwapMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

def coordinateSwap : Coord → Coord := affineCoordinates 0 coordinateSwapMatrix

def swappedMetric (g : MetricField) : MetricField :=
  affinePullbackMetric g 0 coordinateSwapMatrix

@[simp] theorem swapCoordinateIndex_zero : swapCoordinateIndex 0 = 1 := rfl
@[simp] theorem swapCoordinateIndex_one : swapCoordinateIndex 1 = 0 := rfl

@[simp] theorem swapCoordinateIndex_involutive (i : Fin 2) :
    swapCoordinateIndex (swapCoordinateIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem coordinateSwap_apply (p : Coord) (i : Fin 2) :
    coordinateSwap p i = p (swapCoordinateIndex i) := by
  fin_cases i <;>
    simp [coordinateSwap, affineCoordinates, coordinateSwapMatrix,
      dotProduct, Fin.sum_univ_two, swapCoordinateIndex]

@[simp] theorem coordinateSwap_involutive (p : Coord) :
    coordinateSwap (coordinateSwap p) = p := by
  ext i
  simp

@[simp] theorem coordinateSwapMatrix_det : coordinateSwapMatrix.det = -1 := by
  norm_num [coordinateSwapMatrix, Matrix.det_fin_two]

@[simp] theorem swappedMetric_apply (g : MetricField) (p : Coord) (i j : Fin 2) :
    swappedMetric g p i j =
      g (coordinateSwap p) (swapCoordinateIndex i) (swapCoordinateIndex j) := by
  fin_cases i <;> fin_cases j <;>
    simp [swappedMetric, affinePullbackMetric, coordinateSwapMatrix,
      Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
      coordinateSwap, swapCoordinateIndex]

@[simp] theorem swappedMetric_det (g : MetricField) (p : Coord) :
    (swappedMetric g p).det = (g (coordinateSwap p)).det := by
  simp only [Matrix.det_fin_two, swappedMetric_apply,
    swapCoordinateIndex_zero, swapCoordinateIndex_one]
  ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_SixVariableQ
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

def qToPStateIndex (i : Fin 6) : Fin 6 := ![1, 0, 3, 2, 4, 5] i

def qToPState (w : DarbouxState) : DarbouxState := fun i => w (qToPStateIndex i)

def qToPStateLinear : DarbouxState →ₗ[ℝ] DarbouxState where
  toFun := qToPState
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def qToPStateCLM : DarbouxState →L[ℝ] DarbouxState :=
  LinearMap.toContinuousLinearMap qToPStateLinear

@[simp] theorem qToPStateCLM_apply (w : DarbouxState) : qToPStateCLM w = qToPState w := rfl

@[simp] theorem qToPStateIndex_involutive (i : Fin 6) :
    qToPStateIndex (qToPStateIndex i) = i := by
  fin_cases i <;> rfl

@[simp] theorem qToPState_involutive (w : DarbouxState) : qToPState (qToPState w) = w := by
  ext i
  exact congrArg w (qToPStateIndex_involutive i)

@[simp] theorem statePoint_qToPState (w : DarbouxState) :
    statePoint (qToPState w) = coordinateSwap (statePoint w) := by
  ext i
  fin_cases i <;> simp [statePoint, qToPState, qToPStateIndex]

@[simp] theorem stateGradient_qToPState (w : DarbouxState) :
    stateGradient (qToPState w) = coordinateSwap (stateGradient w) := by
  ext i
  fin_cases i <;> simp [stateGradient, qToPState, qToPStateIndex]

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_WarpedMetric
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

def warpedMetric (f : Coord → ℝ) : MetricField :=
  fun p => Matrix.diagonal ![1, (f p) ^ 2]

@[simp] theorem warpedMetric_00 (f : Coord → ℝ) (p : Coord) :
    warpedMetric f p 0 0 = 1 := by simp [warpedMetric]

@[simp] theorem warpedMetric_01 (f : Coord → ℝ) (p : Coord) :
    warpedMetric f p 0 1 = 0 := by simp [warpedMetric]

@[simp] theorem warpedMetric_10 (f : Coord → ℝ) (p : Coord) :
    warpedMetric f p 1 0 = 0 := by simp [warpedMetric]

@[simp] theorem warpedMetric_11 (f : Coord → ℝ) (p : Coord) :
    warpedMetric f p 1 1 = (f p) ^ 2 := by simp [warpedMetric]

@[simp] theorem warpedMetric_det (f : Coord → ℝ) (p : Coord) :
    (warpedMetric f p).det = (f p) ^ 2 := by
  simp [Matrix.det_fin_two]

@[simp] theorem coordPartial_const (i : Fin 2) (c : ℝ) (p : Coord) :
    coordPartial i (fun _ : Coord => c) p = 0 := by
  simp [coordPartial]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_CompactParameterIntegral
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

universe u
namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def compactParameterIntegral (H : Coord × ℝ → F) (p : Coord) : F :=
  ∫ s in Icc (0 : ℝ) 1, H (p,s)

def compactParameterPartial (H : Coord × ℝ → F) (q : Coord × ℝ) : Coord →L[ℝ] F :=
  (fderiv ℝ H q).comp (ContinuousLinearMap.inl ℝ Coord ℝ)

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem parameter_slice_continuousOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D)
    {p : Coord} (hp : p ∈ U) : ContinuousOn (fun s => H (p,s)) (Icc (0 : ℝ) 1) :=
  hH.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hs => hUD ⟨hp,hs⟩)

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem exists_local_parameter_norm_bound
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) :
    ∃ e B : ℝ, 0 < e ∧ 0 ≤ B ∧ Metric.ball p e ⊆ U ∧
      ∀ x ∈ Metric.ball p e, ∀ s ∈ Icc (0 : ℝ) 1, ‖H (x,s)‖ ≤ B := by
  obtain ⟨e,he,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hp)
  let K := Metric.closedBall p (e/2) ×ˢ Icc (0 : ℝ) 1
  have hK : IsCompact K := (isCompact_closedBall p (e/2)).prod isCompact_Icc
  have hKD : K ⊆ D := by
    intro q hq
    exact hUD ⟨hball (Metric.closedBall_subset_ball (half_lt_self he) hq.1),hq.2⟩
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn (hH.mono hKD)
  refine ⟨e/2,max B 0,half_pos he,le_max_right _ _,?_,?_⟩
  · intro x hx
    exact hball ((Metric.ball_subset_ball (half_le_self he.le)) hx)
  · intro x hx s hs
    exact (hB (x,s) ⟨Metric.ball_subset_closedBall hx,hs⟩).trans (le_max_left _ _)

omit [CompleteSpace F] in
theorem compactParameterIntegral_continuousOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContinuousOn H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) : ContinuousOn (compactParameterIntegral H) U := by
  intro p hp
  obtain ⟨e,B,he,hB,hball,hbound⟩ := exists_local_parameter_norm_bound hH hU hUD hp
  have hmeas : ∀ᶠ x in 𝓝 p, AEStronglyMeasurable (fun s => H (x,s))
      (volume.restrict (Icc (0 : ℝ) 1)) := by
    filter_upwards [hU.mem_nhds hp] with x hx
    exact ((parameter_slice_continuousOn hH hUD hx).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  have hdom : ∀ᶠ x in 𝓝 p, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ‖H (x,s)‖ ≤ B := by
    filter_upwards [Metric.ball_mem_nhds p he] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hbound x hx s hs
  have hint : Integrable (fun _ : ℝ => B) (volume.restrict (Icc (0 : ℝ) 1)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hpoint : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ContinuousAt (fun x => H (x,s)) p := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (hH.continuousAt (hD.mem_nhds (hUD ⟨hp,hs⟩))).comp
      (continuous_id.prodMk continuous_const).continuousAt
  exact (continuousAt_of_dominated hmeas hdom hint hpoint).continuousWithinAt

omit [CompleteSpace F] in
theorem compactParameterPartial_contDiffOn
    {H : Coord × ℝ → F} {D : Set (Coord × ℝ)} (hD : IsOpen D) (n : ℕ)
    (hH : ContDiffOn ℝ (n+1 : ℕ) H D) :
    ContDiffOn ℝ n (compactParameterPartial H) D := by
  have hd : ContDiffOn ℝ n (fderiv ℝ H) D := hH.fderiv_of_isOpen hD (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  exact hd.clm_comp contDiffOn_const

omit [CompleteSpace F] in
theorem compactParameter_slice_hasFDerivAt
    {H : Coord × ℝ → F} {D : Set (Coord × ℝ)} (hH : ContDiffOn ℝ 1 H D)
    (hD : IsOpen D) {p : Coord} {s : ℝ} (hp : (p,s) ∈ D) :
    HasFDerivAt (fun x => H (x,s)) (compactParameterPartial H (p,s)) p := by
  have hd := ((hH.contDiffAt (hD.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt
  have hi : HasFDerivAt (fun x : Coord => (x,s)) (ContinuousLinearMap.inl ℝ Coord ℝ) p :=
    hasFDerivAt_prodMk_left p s
  exact hd.comp p hi

omit [CompleteSpace F] in
theorem compactParameterIntegral_hasFDerivAt
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ 1 H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) :
    HasFDerivAt (compactParameterIntegral H)
      (compactParameterIntegral (compactParameterPartial H) p) p := by
  have hpart : ContinuousOn (compactParameterPartial H) D :=
    (compactParameterPartial_contDiffOn hD 0 hH).continuousOn
  obtain ⟨e,B,he,hB,hball,hbound⟩ := exists_local_parameter_norm_bound hpart hU hUD hp
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume.restrict (Icc (0 : ℝ) 1)) (bound := fun _ => B)
    (s := Metric.ball p e) (F' := fun x s => compactParameterPartial H (x,s))
    (Metric.ball_mem_nhds p he)
  · filter_upwards [hU.mem_nhds hp] with x hx
    exact ((parameter_slice_continuousOn hH.continuousOn hUD hx).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  · exact (parameter_slice_continuousOn hH.continuousOn hUD hp).integrableOn_compact isCompact_Icc
  · exact ((parameter_slice_continuousOn hpart hUD hp).integrableOn_compact isCompact_Icc).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    intro x hx
    exact hbound x hx s hs
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    intro x hx
    exact compactParameter_slice_hasFDerivAt hH hD (hUD ⟨hball hx,hs⟩)

theorem compactParameterIntegral_contDiffOn_finite (n : ℕ) :
    ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)},
      ContDiffOn ℝ n H D → IsOpen D → IsOpen U →
      U ×ˢ Icc (0 : ℝ) 1 ⊆ D → ContDiffOn ℝ n (compactParameterIntegral H) U := by
  induction n with
  | zero =>
    intro F _ _ _ H U D hH hD hU hUD
    simpa only [Nat.cast_zero,contDiffOn_zero] using
      compactParameterIntegral_continuousOn hH.continuousOn hD hU hUD
  | succ n ih =>
    intro F _ _ _ H U D hH hD hU hUD
    have hH1 : ContDiffOn ℝ 1 H D := hH.of_le (by exact_mod_cast (show 1 ≤ n+1 by omega))
    have hd (p : Coord) (hp : p ∈ U) := compactParameterIntegral_hasFDerivAt hH1 hD hU hUD hp
    have hpart : ContDiffOn ℝ n (compactParameterPartial H) D :=
      compactParameterPartial_contDiffOn hD n hH
    have hmeanPart : ContDiffOn ℝ n (compactParameterIntegral (compactParameterPartial H)) U :=
      ih hpart hD hU hUD
    have hs : ContDiffOn ℝ ((n : ℕ∞ω)+1) (compactParameterIntegral H) U := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun p hp => (hd p hp).differentiableAt.differentiableWithinAt,by simp,?_⟩
      exact hmeanPart.congr (fun p hp => (hd p hp).fderiv)
    simpa only [Nat.cast_add,Nat.cast_one] using hs

theorem compactParameterIntegral_contDiffOn
    {H : Coord × ℝ → F} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ ∞ H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) :
    ContDiffOn ℝ ∞ (compactParameterIntegral H) U :=
  contDiffOn_infty.mpr (fun n => compactParameterIntegral_contDiffOn_finite n
    (hH.of_le (WithTop.coe_le_coe.mpr le_top)) hD hU hUD)

end SmoothLocal.Analytic

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonCoefficientDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Analytic
open SmoothLocal.Geometry

theorem compactParameterIntegral_coordPartial
    {H : Coord × ℝ → ℝ} {U : Set Coord} {D : Set (Coord × ℝ)}
    (hH : ContDiffOn ℝ ∞ H D) (hD : IsOpen D) (hU : IsOpen U)
    (hUD : U ×ˢ Icc (0 : ℝ) 1 ⊆ D) {p : Coord} (hp : p ∈ U) (j : Fin 2) :
    coordPartial j (compactParameterIntegral H) p =
      ∫ sigma in Icc (0 : ℝ) 1, compactParameterPartial H (p,sigma) (Pi.single j 1) := by
  have hH1 : ContDiffOn ℝ 1 H D := hH.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := compactParameterIntegral_hasFDerivAt hH1 hD hU hUD hp
  have hpart : ContinuousOn (compactParameterPartial H) D :=
    (compactParameterPartial_contDiffOn hD 0 hH1).continuousOn
  have hint : Integrable (fun sigma => compactParameterPartial H (p,sigma))
      (volume.restrict (Icc (0 : ℝ) 1)) :=
    (parameter_slice_continuousOn hpart hUD hp).integrableOn_compact isCompact_Icc
  change fderiv ℝ (compactParameterIntegral H) p (Pi.single j 1) = _
  rw [hd.fderiv]
  exact ContinuousLinearMap.integral_apply hint (Pi.single j 1)

end SmoothLocal.Analytic

end

end OAI
end


