-- Prove2me | Definitions.Def_Q226II006
-- name    : Q226II006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:37:15.17711+00:00
-- url     : https://prove2.me/theorems/bc20f5b8-6daf-4908-8e0d-841cb2c049d5
-- title:
--   Definitions bundle Q226II006 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 97 declarations of OpenAI's Lean: 29 definitions and 68 theorems. The definitions and types are `OAI.SmoothLocal.Geometry.curvatureLowerJet`, `OAI.SmoothLocal.Geometry.inducedMetric`, `OAI.SmoothLocal.Geometry.lowerChristoffelDerivativeJet`, `OAI.SmoothLocal.Geometry.normalResidual`, `OAI.SmoothLocal.Geometry.ordinaryHessian`, `OAI.SmoothLocal.Geometry.orientedCovHessian`, `OAI.SmoothLocal.Geometry.rotatedForm`, `OAI.SmoothLocal.Geometry.secondFundamental`, `OAI.SmoothLocal.Geometry.tangentCross`, `OAI.SmoothLocal.Geometry.unitNormalField`, `OAI.SmoothLocal.Perturbation.SupportedJetProduct`, `OAI.SmoothLocal.Perturbation.supportedJetMap`, `OAI.SmoothLocal.Pulse.curvatureDensity`, `OAI.SmoothLocal.Pulse.curvatureFirstFunction`, `OAI.SmoothLocal.Pulse.forcingCoefficient`, `OAI.SmoothLocal.Pulse.pulseLeadingBound`, `OAI.SmoothLocal.Pulse.pulseMomentWeight`, `OAI.SmoothLocal.Pulse.pulsePrincipalLeading`, `OAI.SmoothLocal.Pulse.pulsePrincipalRemainder`, `OAI.SmoothLocal.Pulse.pulsePrincipalRemainderBound`, `OAI.SmoothLocal.Pulse.spatialCutoffSquare`, `OAI.SmoothLocal.Pulse.thetaCurvatureFirstIncrement`, `OAI.SmoothLocal.Pulse.thetaPulseFirstJet`, `OAI.SmoothLocal.Pulse.thetaPulseMetric`, `OAI.SmoothLocal.Taylor.initialAxisCLM`, `OAI.SmoothLocal.Taylor.linearCauchy`, `OAI.SmoothLocal.Taylor.separatedProduct`, `OAI.SmoothLocal.Taylor.spatialStrip`, `OAI.SmoothLocal.Taylor.taylorCorrection`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Assembly_SupportedSmoothComplete`, `IsometricImmersion_Calculus_ExtremumHessian`, `IsometricImmersion_Caps_PulseReflection`, `IsometricImmersion_Comparison_ClosureMetricApproximation`, `IsometricImmersion_Comparison_ComparisonSourceBounds`, `IsometricImmersion_Curvature_CurvatureLowerTube`, `IsometricImmersion_Darboux_CurvaturePrincipalPart`, `IsometricImmersion_Darboux_QStripJetControl`, `IsometricImmersion_Estimates_ActualQMomentLower`, `IsometricImmersion_Immersions_ActualHeight`, `IsometricImmersion_Immersions_BoundedHeightClasses`, `IsometricImmersion_Immersions_InducedMetric`, `IsometricImmersion_Immersions_NormalField`, `IsometricImmersion_Immersions_OrientedHeightPullback`, `IsometricImmersion_Immersions_RankOneOrientation`, `IsometricImmersion_Metric`, `IsometricImmersion_Metrics_ModelProfile`, `IsometricImmersion_Pulses_ActualForcingCoefficient`, `IsometricImmersion_Pulses_ForcingCoefficientSign`, `IsometricImmersion_Pulses_PulseCurvaturePrincipal`, `IsometricImmersion_Pulses_PulseDensitySlab`, `IsometricImmersion_Pulses_PulseMoment`, `IsometricImmersion_Pulses_PulseMomentError`, `IsometricImmersion_Pulses_PulseMomentGeometry`, `IsometricImmersion_Pulses_PulseProfiles`, `IsometricImmersion_Pulses_PulseSecondXi`, `IsometricImmersion_Pulses_QReferenceForcingMargins`, `IsometricImmersion_Taylor_FiniteTaylorComparison`, `IsometricImmersion_Taylor_TaylorCoefficientBounds`, `IsometricImmersion_Taylor_TaylorPolynomialJetBounds`, `IsometricImmersion_Taylor_TaylorQJetBounds`, `IsometricImmersion_Taylor_TaylorSeparatedProduct`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II000`, `Q226II001` and `Q226II002` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II009` and `Q226II010`.
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
import Mathlib.Topology.Homeomorph.Lemmas
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
import Definitions.Def_Q226II000
import Definitions.Def_Q226II001
import Definitions.Def_Q226II002

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

def secondFundamental (F : Coord → Ambient) (n : Ambient) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => inner ℝ (coordPartial i (coordPartial j F) p) n

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_ModelProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Model
open SmoothLocal.Geometry

theorem modelProfile_plateau {y : ℝ} (hy : y ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    modelProfile y = 1 := by
  have hs : y ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := sq_le_sq' hy.1 hy.2
  have hz := squareTransition_zero (t := y ^ 2) (by nlinarith)
  simp [modelProfile, hz]

theorem modelCurvature_central_square {kappa : ℝ} (hkappa : 0 < kappa) {p : Coord}
    (hp : ∀ i : Fin 2, p i ∈ Icc (-(1 / 5 : ℝ)) (1 / 5)) :
    modelCurvature kappa p < -kappa / 2 := by
  have hplateau : modelProfile (p 1) = 1 := modelProfile_plateau
    ⟨by linarith [(hp 1).1], by linarith [(hp 1).2]⟩
  have hx : (p 0) ^ 2 ≤ (1 / 5 : ℝ) ^ 2 := sq_le_sq' (hp 0).1 (hp 0).2
  have hmul := mul_le_mul_of_nonneg_left hx hkappa.le
  unfold modelCurvature
  rw [hplateau]
  nlinarith

end SmoothLocal.Model

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_InducedMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter
namespace SmoothLocal.Geometry

def inducedMetric (F : Coord → Ambient) : MetricField := fun p i j =>
  inner ℝ (coordPartial i F p) (coordPartial j F p)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_ActualHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators
namespace SmoothLocal.Geometry

def normalResidual (g : MetricField) (F : Coord → Ambient) (p : Coord) :
    Fin 2 → Fin 2 → Ambient := fun i j =>
  coordPartial i (coordPartial j F) p - ∑ k, christoffel g k i j p • coordPartial k F p

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Assembly_SupportedSmoothComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter TopologicalSpace
open scoped BoundedContinuousFunction

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

abbrev SupportedJetProduct (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :=
  Π k : ℕ, Coord →ᵇ (Coord [×k]→L[ℝ] V)

def supportedJetMap (K : Compacts Coord) :
    ContDiffMapSupportedIn Coord V ⊤ K →L[ℝ] SupportedJetProduct V :=
  ContinuousLinearMap.pi (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤)

omit [CompleteSpace V] in
theorem supportedJetMap_isUniformEmbedding (K : Compacts Coord) :
    IsUniformEmbedding (supportedJetMap K :
      ContDiffMapSupportedIn Coord V ⊤ K → SupportedJetProduct V) :=
  ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM (𝕜 := ℝ) (n := ⊤)

set_option synthInstance.maxHeartbeats 400000 in
omit [CompleteSpace V] in
theorem supportedJetMap_isClosed_range (K : Compacts Coord) :
    IsClosed (Set.range (supportedJetMap K :
      ContDiffMapSupportedIn Coord V ⊤ K → SupportedJetProduct V)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu ht
  choose f hf using hu
  have hfconv : Tendsto (fun n => supportedJetMap K (f n)) atTop (𝓝 v) := by
    simpa only [hf] using ht
  have hconv (k : ℕ) : TendstoUniformly
      (fun n => iteratedFDeriv ℝ k (f n)) (v k) atTop := by
    have hcoord := ((continuous_apply k).tendsto v).comp hfconv
    change Tendsto (fun n => ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k (f n))
      atTop (𝓝 (v k)) at hcoord
    have h := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hcoord
    simpa only [ContDiffMapSupportedIn.structureMapCLM_top_apply] using h
  let C (k : ℕ) :=
    continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Coord) V
  have hderivative (k : ℕ) (x : Coord) :
      HasFDerivAt (fun y => v k y) (C k (v (k + 1) x)) x := by
    have hnext : TendstoUniformly
        (fun n => C k ∘ iteratedFDeriv ℝ (k + 1) (f n)) (C k ∘ v (k + 1)) atTop :=
      (C k).isometry.uniformContinuous.comp_tendstoUniformly (hconv (k + 1))
    have hfn (n : ℕ) (y : Coord) : HasFDerivAt (iteratedFDeriv ℝ k (f n))
        (C k (iteratedFDeriv ℝ (k + 1) (f n) y)) y := by
      have hs : ContDiff ℝ ∞ (f n) := (f n).contDiff
      have hd := ((hs.contDiffAt (x := y)).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).hasFDerivAt
      simpa only [fderiv_iteratedFDeriv, Function.comp_apply, C] using hd
    exact hasFDerivAt_of_tendstoUniformly hnext hfn (fun y => (hconv k).tendsto_at y) x
  let C0 := continuousMultilinearCurryFin0 ℝ Coord V
  let g : Coord → V := fun x => C0 (v 0 x)
  have hjet : ∀ k : ℕ, iteratedFDeriv ℝ k g = (v k : Coord → Coord [×k]→L[ℝ] V) := by
    intro k
    induction k with
    | zero =>
        funext x
        change C0.symm (C0 (v 0 x)) = v 0 x
        exact C0.symm_apply_apply _
    | succ k ih =>
        rw [iteratedFDeriv_succ_eq_comp_left, ih]
        funext x
        change (C k).symm (fderiv ℝ (fun y => v k y) x) = v (k + 1) x
        rw [(hderivative k x).fderiv]
        exact (C k).symm_apply_apply _
  have hg : ContDiff ℝ ∞ g := by
    apply contDiff_iff_continuous_differentiable.mpr
    constructor
    · intro k _
      rw [hjet k]
      exact (v k).continuous
    · intro k _
      rw [hjet k]
      exact fun x => (hderivative k x).differentiableAt
  have hzero : EqOn g 0 (K : Set Coord)ᶜ := by
    intro x hx
    have hlim := (hconv 0).tendsto_at x
    have hconst : Tendsto (fun n => iteratedFDeriv ℝ 0 (f n) x) atTop (𝓝 0) := by
      have hz (n : ℕ) : iteratedFDeriv ℝ 0 (f n) x = 0 :=
        (f n).iteratedFDeriv_zero_on_compl hx
      simpa only [hz] using (tendsto_const_nhds (x := (0 : Coord [×0]→L[ℝ] V)))
    have hvzero : v 0 x = 0 := tendsto_nhds_unique hlim hconst
    change C0 (v 0 x) = 0
    rw [hvzero, map_zero]
  let φ : ContDiffMapSupportedIn Coord V ⊤ K := ⟨g, hg, hzero⟩
  refine ⟨φ, ?_⟩
  funext k
  apply BoundedContinuousFunction.ext
  intro x
  change ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ k φ x = v k x
  rw [ContDiffMapSupportedIn.structureMapCLM_top_apply]
  exact congrFun (hjet k) x

theorem supportedSmooth_completelyMetrizable (K : Compacts Coord) :
    IsCompletelyMetrizableSpace (ContDiffMapSupportedIn Coord V ⊤ K) := by
  have (k : ℕ) : IsCompletelyMetrizableSpace (Coord →ᵇ (Coord [×k]→L[ℝ] V)) := by
    have hc : CompleteSpace (Coord →ᵇ (Coord [×k]→L[ℝ] V)) := inferInstance
    refine ⟨⟨inferInstance, ?_, ?_⟩⟩
    · rfl
    · exact hc
  have : IsCompletelyMetrizableSpace (SupportedJetProduct V) := inferInstance
  have he : Topology.IsClosedEmbedding (supportedJetMap K :
      ContDiffMapSupportedIn Coord V ⊤ K → SupportedJetProduct V) :=
    ⟨(supportedJetMap_isUniformEmbedding K).isEmbedding, supportedJetMap_isClosed_range K⟩
  exact he.IsCompletelyMetrizableSpace

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_ExtremumHessian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

def ordinaryHessian (z : Coord → ℝ) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => coordPartial i (coordPartial j z) p

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_CurvaturePrincipalPart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def lowerChristoffelDerivativeJet (G : MetricMatrix) (D : MetricFirstJet)
    (d k i j : Fin 2) : ℝ :=
  (1/2 : ℝ) * ∑ l, inverseDerivativeJet G D d k l * (D i j l+D j i l-D l i j)

def curvatureLowerJet (G : MetricMatrix) (D : MetricFirstJet) : ℝ :=
  ∑ l, G 0 l * (lowerChristoffelDerivativeJet G D 0 l 1 1 -
    lowerChristoffelDerivativeJet G D 1 l 0 1 +
    ∑ m, (christoffelJet G D m 1 1 * christoffelJet G D l 0 m -
      christoffelJet G D m 0 1 * christoffelJet G D l 1 m))

theorem metric_inverse_first_row_contraction (G : MetricMatrix) (hdet : G.det ≠ 0)
    (T : Fin 2 → ℝ) :
    (∑ l, G 0 l * ∑ a, G⁻¹ l a * T a) = T 0 := by
  have hi := Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hdet)
  have h0 := congrFun (congrFun hi 0) 0
  have h1 := congrFun (congrFun hi 0) 1
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply,ite_true, if_true,
    show (0 : Fin 2) ≠ 1 by decide,ite_false, if_false] at h0 h1
  calc
    _ = (G 0 0*G⁻¹ 0 0+G 0 1*G⁻¹ 1 0)*T 0 +
        (G 0 0*G⁻¹ 0 1+G 0 1*G⁻¹ 1 1)*T 1 := by
      simp only [Fin.sum_univ_two]
      ring
    _ = T 0 := by rw [h0,h1]; ring

theorem curvatureJet_density_raw (G : MetricMatrix) (D : MetricFirstJet)
    (DD : MetricSecondJet) (hdet : G.det ≠ 0) :
    curvatureJet G D DD * G.det =
      (1/2 : ℝ)*(DD 0 1 1 0+DD 0 1 1 0-DD 0 0 1 1-
        DD 1 0 1 0-DD 1 1 0 0+DD 1 0 0 1) + curvatureLowerJet G D := by
  let T : Fin 2 → ℝ := fun a => DD 0 1 1 a+DD 0 1 1 a-DD 0 a 1 1-
    DD 1 0 1 a-DD 1 1 0 a+DD 1 a 0 1
  have hc := metric_inverse_first_row_contraction G hdet T
  simp only [T,Fin.sum_univ_two] at hc
  rw [curvatureJet,div_mul_cancel₀ _ hdet]
  simp only [riemannJet,christoffelDerivativeJet,curvatureLowerJet,
    lowerChristoffelDerivativeJet,Fin.sum_univ_two]
  linear_combination (1/2 : ℝ)*hc

section SmoothLowerJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {S : Set E} {G : E → MetricMatrix} {D : E → MetricFirstJet}

theorem inverseDerivativeJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (d i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => inverseDerivativeJet (G s) (D s) d i j) S := by
  have hi := metricMatrix_inverse_contDiffOn hG hdet
  have ht (a b : Fin 2) :
      ContDiffOn ℝ ∞ (fun s => (G s)⁻¹ i a * D s d a b * (G s)⁻¹ b j) S :=
    ((hi i a).mul (hD d a b)).mul (hi b j)
  simpa only [inverseDerivativeJet,Fin.sum_univ_two] using
    (((ht 0 0).add (ht 0 1)).add ((ht 1 0).add (ht 1 1))).neg

theorem lowerChristoffelDerivativeJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) (d k i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun s => lowerChristoffelDerivativeJet (G s) (D s) d k i j) S := by
  have hi := inverseDerivativeJet_contDiffOn hG hD hdet
  have ht (l : Fin 2) : ContDiffOn ℝ ∞
      (fun s => inverseDerivativeJet (G s) (D s) d k l *
        (D s i j l+D s j i l-D s l i j)) S :=
    (hi d k l).mul (((hD i j l).add (hD j i l)).sub (hD l i j))
  simpa only [lowerChristoffelDerivativeJet,Fin.sum_univ_two] using
    (contDiffOn_const (c := (1/2 : ℝ))).mul ((ht 0).add (ht 1))

theorem curvatureLowerJet_contDiffOn
    (hG : ∀ i j, ContDiffOn ℝ ∞ (fun s => G s i j) S)
    (hD : ∀ d i j, ContDiffOn ℝ ∞ (fun s => D s d i j) S)
    (hdet : ∀ s ∈ S, (G s).det ≠ 0) :
    ContDiffOn ℝ ∞ (fun s => curvatureLowerJet (G s) (D s)) S := by
  have hΓ := christoffelJet_contDiffOn hG hD hdet
  have hΓD := lowerChristoffelDerivativeJet_contDiffOn hG hD hdet
  have ht (l m : Fin 2) : ContDiffOn ℝ ∞ (fun s =>
      christoffelJet (G s) (D s) m 1 1 * christoffelJet (G s) (D s) l 0 m -
        christoffelJet (G s) (D s) m 0 1 * christoffelJet (G s) (D s) l 1 m) S :=
    ((hΓ m 1 1).mul (hΓ l 0 m)).sub ((hΓ m 0 1).mul (hΓ l 1 m))
  have hl (l : Fin 2) : ContDiffOn ℝ ∞ (fun s => G s 0 l *
      (lowerChristoffelDerivativeJet (G s) (D s) 0 l 1 1 -
        lowerChristoffelDerivativeJet (G s) (D s) 1 l 0 1 +
        ∑ m, (christoffelJet (G s) (D s) m 1 1 * christoffelJet (G s) (D s) l 0 m -
          christoffelJet (G s) (D s) m 0 1 * christoffelJet (G s) (D s) l 1 m))) S := by
    simpa only [Fin.sum_univ_two] using
      (hG 0 l).mul (((hΓD 0 l 1 1).sub (hΓD 1 l 0 1)).add ((ht l 0).add (ht l 1)))
  simpa only [curvatureLowerJet,Fin.sum_univ_two] using (hl 0).add (hl 1)

end SmoothLowerJet

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise Distributions
open Set Filter

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Perturbation

theorem axisBump_pos {a t : ℝ} (ha : 0 < a) (ht : |t| < a) : 0 < axisBump a t := by
  have hs : |t| ^ 2 < a ^ 2 := (sq_lt_sq₀ (abs_nonneg t) ha.le).mpr ht
  exact expNegInvGlue.pos_of_pos (sub_pos.mpr (by simpa only [sq_abs] using hs))

theorem axisBump_pos_zero {a : ℝ} (ha : 0 < a) : 0 < axisBump a 0 :=
  axisBump_pos ha (by simpa using ha)

theorem axisBump_integral_pos {a : ℝ} (ha : 0 < a) : 0 < ∫ t : ℝ, axisBump a t :=
  (axisBump_contDiff a).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (axisBump_hasCompactSupport ha) (axisBump_nonneg a) (axisBump_pos_zero ha).ne'

theorem temporalCutoff_integral_pos : 0 < ∫ t : ℝ, temporalCutoff t :=
  axisBump_integral_pos (by norm_num)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseCurvaturePrincipal
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def thetaPulseMetric (g : MetricField) (f : Coord → ℝ) : MetricField :=
  fun p => g p + !![0,0;0,f p]

def thetaPulseFirstJet (f : Coord → ℝ) (p : Coord) : MetricFirstJet :=
  fun d i j => if i=1 ∧ j=1 then coordPartial d f p else 0

theorem thetaPulseMetric_entry (g : MetricField) (f : Coord → ℝ) (p : Coord) (i j : Fin 2) :
    thetaPulseMetric g f p i j = g p i j + if i=1 ∧ j=1 then f p else 0 := by
  fin_cases i <;> fin_cases j <;> simp [thetaPulseMetric]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_PulseReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Flow.Reflection

theorem axisBump_even (a t : ℝ) : axisBump a (-t) = axisBump a t := by
  simp only [axisBump, neg_sq]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ClosureMetricApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise Distributions

namespace SmoothLocal.Perturbation
open SmoothLocal.Geometry

theorem metricCoefficientCLM_norm_le (i j : Fin 2) :
    ‖(show (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ from metricCoefficientCLM i j)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ActualForcingCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def forcingCoefficient (g : MetricField) (z : Coord → ℝ) (p : Coord) : ℝ :=
  (1 - covectorNormSq g z p) / (2 * covHessian g z p 0 0)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_CurvatureLowerTube
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def curvatureFirstFunction (a : CurvatureFirstInput) : ℝ := curvatureLowerJet a.1 a.2

def thetaCurvatureFirstIncrement (f : Coord → ℝ) (p : Coord) : CurvatureFirstInput :=
  ((fun i j => (!![0,0;0,f p] : MetricMatrix) i j),
    (fun d i j => thetaPulseFirstJet f p d i j))

theorem curvatureFirstFunction_contDiffOn :
    ContDiffOn ℝ ∞ curvatureFirstFunction curvatureFirstDomain :=
  curvatureLowerJet_contDiffOn (fun i j => by fun_prop)
    (fun d i j => by fun_prop) (fun _ h => h)

theorem curvatureFirstTube_fderiv_bound (M : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a ∈ curvatureFirstTube M d,
      ‖fderiv ℝ curvatureFirstFunction a‖ ≤ C := by
  have hcont : ContinuousOn (fderiv ℝ curvatureFirstFunction) curvatureFirstDomain :=
    (curvatureFirstFunction_contDiffOn.fderiv_of_isOpen (m := 0)
      curvatureFirstDomain_isOpen (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousOn
  obtain ⟨C,hC⟩ := (curvatureFirstTube_isCompact M d).exists_bound_of_continuousOn
    (hcont.mono (curvatureFirstTube_subset_domain M hd))
  exact ⟨max C 0,le_max_right _ _,fun a ha => (hC a ha).trans (le_max_left _ _)⟩

theorem theta_first_segment_det (a : CurvatureFirstInput) (f : Coord → ℝ) (p : Coord)
    (t : ℝ) :
    (Matrix.of ((1-t) • a + t • (a+thetaCurvatureFirstIncrement f p)).1).det =
      (1-t)*(Matrix.of a.1).det+t*(Matrix.of (a+thetaCurvatureFirstIncrement f p).1).det := by
  simp only [Matrix.det_fin_two,thetaCurvatureFirstIncrement,Prod.fst_add,Prod.smul_fst,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.of_apply]
  ring

theorem theta_first_segment_subset_tube (a : CurvatureFirstInput) (f : Coord → ℝ) (p : Coord)
    {M d : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖a+thetaCurvatureFirstIncrement f p‖ ≤ M)
    (hda : d ≤ (Matrix.of a.1).det)
    (hdb : d ≤ (Matrix.of (a+thetaCurvatureFirstIncrement f p).1).det) :
    segment ℝ a (a+thetaCurvatureFirstIncrement f p) ⊆ curvatureFirstTube M d := by
  intro x hx
  have hball : x ∈ Metric.closedBall (0 : CurvatureFirstInput) M :=
    (convex_closedBall (0 : CurvatureFirstInput) M).segment_subset
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using ha)
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using hb) hx
  refine ⟨hball,?_⟩
  rw [segment_eq_image] at hx
  obtain ⟨t,ht,rfl⟩ := hx
  change d ≤ (Matrix.of ((1-t) • a + t • (a+thetaCurvatureFirstIncrement f p)).1).det
  rw [theta_first_segment_det]
  have h0 := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hda)
  have h1 := mul_nonneg ht.1 (sub_nonneg.mpr hdb)
  nlinarith

theorem thetaCurvatureFirstIncrement_norm_le (f : Coord → ℝ) (p : Coord) {e : ℝ}
    (he : 0 ≤ e) (hf : |f p| ≤ e) (hdf : ∀ i, |coordPartial i f p| ≤ e) :
    ‖thetaCurvatureFirstIncrement f p‖ ≤ e := by
  change max ‖(!![0,0;0,f p] : MetricMatrix)‖ ‖thetaPulseFirstJet f p‖ ≤ e
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    fin_cases i <;> fin_cases j
    · simpa using he
    · simpa using he
    · simpa using he
    · simpa [Matrix.of_apply,Real.norm_eq_abs] using hf
  · apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    simp only [thetaPulseFirstJet,Real.norm_eq_abs]
    split_ifs
    · exact hdf d
    · simpa using he

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseSecondXi
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted

theorem pulseXiLine_hasDerivAt (a : ℝ) (N : ℕ) (delta tau x y : ℝ) :
    HasDerivAt
      (fun u => (1/tau^N)*temporalCutoff (tau*y/delta)*
        (deriv (axisBump a) u*Real.cos (tau*u)-tau*axisBump a u*Real.sin (tau*u)))
      ((1/tau^N)*temporalCutoff (tau*y/delta)*
        (deriv (deriv (axisBump a)) x*Real.cos (tau*x)-
          2*tau*deriv (axisBump a) x*Real.sin (tau*x)-
            tau^2*axisBump a x*Real.cos (tau*x))) x := by
  have hχ := ((axisBump_contDiff a).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasDerivAt
  have hχ' := (((contDiff_infty_iff_deriv.mp (axisBump_contDiff a)).2).differentiable
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasDerivAt
  have hc := (Real.hasDerivAt_cos (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have hs := (Real.hasDerivAt_sin (tau*x)).comp x ((hasDerivAt_id x).const_mul tau)
  have h := (((hχ'.mul hc).sub ((hχ.const_mul tau).mul hs)).const_mul
    ((1/tau^N)*temporalCutoff (tau*y/delta)))
  simp only [Function.comp_def, Pi.mul_def, Pi.sub_def, mul_one] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

def pulsePrincipalLeading (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  (tau^2/(2*tau^N))*axisBump a (p 0)*temporalCutoff (tau*p 1/delta)*Real.cos (tau*p 0)

def pulsePrincipalRemainder (a : ℝ) (N : ℕ) (delta tau : ℝ) (p : Coord) : ℝ :=
  (1/tau^N)*temporalCutoff (tau*p 1/delta)*
    (tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
      (1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0))

def pulsePrincipalRemainderBound (a : ℝ) (ha : 0 < a) : ℝ :=
  axisBumpDerivativeBound (1/2) (by norm_num) 0 *
    (axisBumpDerivativeBound a ha 1+axisBumpDerivativeBound a ha 2)

theorem pulsePrincipalRemainderBound_nonneg (a : ℝ) (ha : 0 < a) :
    0 ≤ pulsePrincipalRemainderBound a ha := by
  exact mul_nonneg (axisBumpDerivativeBound_pos (by norm_num) 0).le
    (add_nonneg (axisBumpDerivativeBound_pos ha 1).le (axisBumpDerivativeBound_pos ha 2).le)

theorem pulse_principal_remainder_le {a : ℝ} (ha : 0 < a) (N : ℕ)
    (delta : ℝ) {tau : ℝ} (ht : 1 ≤ tau) (p : Coord) :
    |pulsePrincipalRemainder a N delta tau p| ≤
      pulsePrincipalRemainderBound a ha * tau/tau^N := by
  let A1 := axisBumpDerivativeBound a ha 1
  let A2 := axisBumpDerivativeBound a ha 2
  let P0 := axisBumpDerivativeBound (1/2) (by norm_num) 0
  have hA1 : 0 ≤ A1 := (axisBumpDerivativeBound_pos ha 1).le
  have hA2 : 0 ≤ A2 := (axisBumpDerivativeBound_pos ha 2).le
  have hP0 : 0 ≤ P0 := (axisBumpDerivativeBound_pos (by norm_num) 0).le
  have ht0 : 0 < tau := zero_lt_one.trans_le ht
  have hq : 0 ≤ (1/tau^N) := div_nonneg zero_le_one (pow_nonneg ht0.le N)
  have hχ1 : |deriv (axisBump a) (p 0)| ≤ A1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_one,Real.norm_eq_abs]
      using axisBump_derivative_le ha 1 (p 0)
  have hχ2 : |deriv (deriv (axisBump a)) (p 0)| ≤ A2 := by
    simpa only [A2,norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      show 2=1+1 by omega,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero,Real.norm_eq_abs]
      using axisBump_derivative_le ha 2 (p 0)
  have hφ : |temporalCutoff (tau*p 1/delta)| ≤ P0 := by
    simpa only [P0,temporalCutoff,norm_iteratedFDeriv_zero,Real.norm_eq_abs]
      using axisBump_derivative_le (by norm_num : (0 : ℝ)<1/2) 0 (tau*p 1/delta)
  have hinner : |tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
      (1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)| ≤ tau*(A1+A2) := by
    calc
      _ ≤ |tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)|+
          |(1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)| := abs_sub _ _
      _ = tau*|deriv (axisBump a) (p 0)| *|Real.sin (tau*p 0)|+
          (1/2 : ℝ)*|deriv (deriv (axisBump a)) (p 0)| *|Real.cos (tau*p 0)| := by
        simp only [abs_mul,abs_of_pos ht0]
        norm_num
      _ ≤ tau*A1*1+(1/2 : ℝ)*A2*1 := by
        exact add_le_add
          (mul_le_mul (mul_le_mul_of_nonneg_left hχ1 ht0.le) (Real.abs_sin_le_one _)
            (abs_nonneg _) (mul_nonneg ht0.le hA1))
          (mul_le_mul (mul_le_mul_of_nonneg_left hχ2 (by norm_num)) (Real.abs_cos_le_one _)
            (abs_nonneg _) (mul_nonneg (by norm_num) hA2))
      _ ≤ tau*(A1+A2) := by nlinarith [mul_le_mul_of_nonneg_right ht hA2]
  calc
    _ = (1/tau^N)*|temporalCutoff (tau*p 1/delta)| *
        |tau*deriv (axisBump a) (p 0)*Real.sin (tau*p 0)-
          (1/2 : ℝ)*deriv (deriv (axisBump a)) (p 0)*Real.cos (tau*p 0)| := by
      simp only [pulsePrincipalRemainder,abs_mul,abs_of_nonneg hq]
    _ ≤ ((1/tau^N)*P0)*(tau*(A1+A2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hφ hq) hinner (abs_nonneg _)
        (mul_nonneg hq hP0)
    _ = pulsePrincipalRemainderBound a ha*tau/tau^N := by
      dsimp only [A1,A2,P0,pulsePrincipalRemainderBound]
      ring

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

def curvatureDensity (g : MetricField) (p : Coord) : ℝ :=
  gaussianCurvature g p*(g p).det

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_ForcingCoefficientSign
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem closedRectangle_eq_Icc (l r b t : ℝ) :
    closedRectangle l r b t = Icc (![l,b]) (![r,t]) := by
  ext p
  change (p 0 ∈ Icc l r ∧ p 1 ∈ Icc b t) ↔
    (![l,b] ≤ p ∧ p ≤ ![r,t])
  constructor
  · intro hp
    constructor <;> intro i <;> fin_cases i
    · exact hp.1.1
    · exact hp.2.1
    · exact hp.1.2
    · exact hp.2.2
  · intro hp
    exact ⟨⟨hp.1 0,hp.2 0⟩,⟨hp.1 1,hp.2 1⟩⟩

theorem closedRectangle_isPreconnected (l r b t : ℝ) :
    IsPreconnected (closedRectangle l r b t) := by
  rw [closedRectangle_eq_Icc]
  exact (convex_Icc (![l,b] : Coord) (![r,t])).isPreconnected

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse

def spatialCutoffSquare (a x : ℝ) : ℝ := axisBump a x^2

theorem spatialCutoffSquare_contDiff (a : ℝ) : ContDiff ℝ ∞ (spatialCutoffSquare a) :=
  (axisBump_contDiff a).pow 2

theorem spatialCutoffSquare_hasCompactSupport {a : ℝ} (ha : 0 < a) :
    HasCompactSupport (spatialCutoffSquare a) := by
  change HasCompactSupport (fun x => axisBump a x ^ 2)
  simpa only [pow_two,Pi.mul_def] using
    (axisBump_hasCompactSupport ha).mul_right (f' := axisBump a)

theorem spatialCutoffSquare_integral_pos {a : ℝ} (ha : 0 < a) :
    0 < ∫ x : ℝ, spatialCutoffSquare a x :=
  (spatialCutoffSquare_contDiff a).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (spatialCutoffSquare_hasCompactSupport ha) (fun _ => sq_nonneg _)
      (sq_pos_of_pos (axisBump_pos_zero ha)).ne'

theorem spatialCutoff_cos_sq_moment_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun tau : ℝ => ∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2) atTop
      (𝓝 ((1/2 : ℝ)*(∫ x : ℝ, axisBump a x^2))) :=
  compact_weight_cos_sq_integral_tendsto (spatialCutoffSquare_contDiff a)
    (spatialCutoffSquare_hasCompactSupport ha)

theorem spatialCutoff_cos_sq_moment_eventually_lower {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ tau : ℝ in atTop,
      c ≤ ∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2 := by
  let I : ℝ := ∫ x : ℝ, axisBump a x^2
  have hI : 0 < I := spatialCutoffSquare_integral_pos ha
  refine ⟨I/4,div_pos hI (by norm_num),?_⟩
  have hgap : I/4 < (1/2 : ℝ)*I := by linarith
  have h := (spatialCutoff_cos_sq_moment_tendsto ha).eventually (eventually_gt_nhds hgap)
  exact h.mono (fun _ ht => ht.le)

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseMomentGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Interval

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

def pulseMomentWeight (a delta tau : ℝ) (q : ℝ × ℝ) : ℝ :=
  temporalCutoff (tau*q.1/delta)*(axisBump a q.2^2*Real.cos (tau*q.2)^2)

theorem pulseMomentWeight_continuous (a delta tau : ℝ) :
    Continuous (pulseMomentWeight a delta tau) := by
  unfold pulseMomentWeight temporalCutoff
  exact (((axisBump_contDiff (1/2)).continuous.comp (by fun_prop)).mul
    ((((axisBump_contDiff a).continuous.comp continuous_snd).pow 2).mul (by fun_prop)))

theorem pulseMomentWeight_nonneg (a delta tau : ℝ) (q : ℝ × ℝ) :
    0 ≤ pulseMomentWeight a delta tau q :=
  mul_nonneg (axisBump_nonneg _ _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem spatial_moment_Icc_eq {a : ℝ} (ha : 0 < a) (tau : ℝ) :
    (∫ x in Icc (-a) a, axisBump a x^2*Real.cos (tau*x)^2) =
      ∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2 := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : axisBump a x = 0 := by
    by_contra hn
    have h := abs_lt.mp (axisBump_support_bound ha hn)
    exact hx ⟨h.1.le,h.2.le⟩
  simp only [hz,zero_pow (by norm_num : (2 : ℕ) ≠ 0),zero_mul]

theorem temporal_pulse_integral {delta tau : ℝ} (hd : 0 < delta) (ht : 0 < tau) :
    (∫ theta in Icc (-(delta/tau)) (delta/tau), temporalCutoff (tau*theta/delta)) =
      (delta/tau)*(∫ theta : ℝ, temporalCutoff theta) := by
  have hglobal : (∫ theta : ℝ, temporalCutoff (tau*theta/delta)) =
      (delta/tau)*(∫ theta : ℝ, temporalCutoff theta) := by
    have heq : (fun theta : ℝ => temporalCutoff (tau*theta/delta)) =
        fun theta => temporalCutoff ((tau/delta)*theta) := by
      funext theta
      congr 1
      ring
    rw [heq,Measure.integral_comp_mul_left]
    simp only [inv_div,abs_of_pos (div_pos hd ht),smul_eq_mul]
  rw [←hglobal]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro theta htheta
  by_contra hn
  have h := axisBump_support_bound (by norm_num : (0 : ℝ) < 1/2) hn
  rw [abs_div,abs_mul,abs_of_pos ht,abs_of_pos hd] at h
  have hmul : tau*|theta| < delta/2 := by
    have hh := (div_lt_iff₀ hd).mp h
    linarith
  have htheta' : |theta| ≤ delta/tau := (le_div_iff₀ ht).mpr (by nlinarith)
  exact htheta (abs_le.mp htheta')

theorem pulseMomentWeight_integral {a delta tau : ℝ}
    (ha : 0 < a) (hd : 0 < delta) (ht : 0 < tau) :
    (∫ q in pulsePairRectangle a delta tau, pulseMomentWeight a delta tau q
      ∂volume.prod volume) =
      (delta/tau)*(∫ theta : ℝ, temporalCutoff theta)*
        (∫ x : ℝ, axisBump a x^2*Real.cos (tau*x)^2) := by
  rw [show pulsePairRectangle a delta tau =
    Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a from rfl]
  unfold pulseMomentWeight
  rw [setIntegral_prod_mul (fun theta : ℝ => temporalCutoff (tau*theta/delta))
    (fun x : ℝ => axisBump a x^2*Real.cos (tau*x)^2)
    (Icc (-(delta/tau)) (delta/tau)) (Icc (-a) a),
    temporal_pulse_integral hd ht,spatial_moment_Icc_eq ha tau]

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_PulseMomentError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem axisBump_Icc_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in Icc (-a) a, axisBump a x) = ∫ x : ℝ, axisBump a x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra hn
  have h := abs_lt.mp (axisBump_support_bound ha hn)
  exact hx ⟨h.1.le,h.2.le⟩

theorem pulse_spatial_mass_integral {a delta tau : ℝ}
    (ha : 0 < a) (hd : 0 ≤ delta) (ht : 0 < tau) :
    (∫ q in pulsePairRectangle a delta tau, axisBump a q.2 ∂volume.prod volume) =
      (2*delta/tau)*(∫ x : ℝ, axisBump a x) := by
  have hw : -(delta/tau) ≤ delta/tau := by linarith [div_nonneg hd ht.le]
  have hh := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun _ : ℝ => (1 : ℝ)) (axisBump a) (Icc (-(delta/tau)) (delta/tau)) (Icc (-a) a)
  simp only [one_mul] at hh
  rw [show pulsePairRectangle a delta tau =
    Icc (-(delta/tau)) (delta/tau) ×ˢ Icc (-a) a from rfl,hh,
    setIntegral_const,Real.volume_real_Icc_of_le hw,smul_eq_mul,mul_one,axisBump_Icc_integral ha]
  ring

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

theorem pulsePrincipalLeading_contDiff (a : ℝ) (N : ℕ) (delta tau : ℝ) :
    ContDiff ℝ ∞ (pulsePrincipalLeading a N delta tau) := by
  unfold pulsePrincipalLeading temporalCutoff
  exact ((contDiff_const.mul ((axisBump_contDiff a).comp (contDiff_apply ℝ ℝ 0))).mul
    ((axisBump_contDiff (1/2)).comp
      ((contDiff_const.mul (contDiff_apply ℝ ℝ 1)).div_const delta))).mul
      (Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0)))

end SmoothLocal.Pulse

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorSeparatedProduct
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det
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

def spatialStrip (I : Set ℝ) : Set Coord := {p | p 0 ∈ I}

theorem spatialStrip_isOpen {I : Set ℝ} (hI : IsOpen I) : IsOpen (spatialStrip I) :=
  hI.preimage (continuous_apply 0)

def separatedProduct (C f : ℝ → ℝ) (p : Coord) : ℝ := C (p 0) * f (p 1)

theorem separatedProduct_contDiffOn {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (separatedProduct C f) (spatialStrip I) :=
  (hC.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).mul
    (hf.comp (contDiff_apply ℝ ℝ 1)).contDiffOn

theorem initialPoint_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y : ℝ => (![y, t] : Coord)) (Pi.single 0 (1 : ℝ)) x := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert hasDerivAt_id x using 1 <;> rfl
  · simpa using hasDerivAt_const x t

theorem point_eta (p : Coord) : (![p 0, p 1] : Coord) = p := by
  ext i
  fin_cases i <;> rfl

theorem separatedProduct_partial_x {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (separatedProduct C f) p = deriv C (p 0) * f (p 1) := by
  have hd := (((separatedProduct_contDiffOn hC f hf).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hd' : HasFDerivAt (separatedProduct C f) (fderiv ℝ (separatedProduct C f) p)
      (![p 0, p 1] : Coord) := by simpa only [point_eta] using hd
  have hcurve := hd'.comp_hasDerivAt (p 0) (initialPoint_hasDerivAt (p 0) (p 1))
  have hCderiv := ((hC.contDiffAt (hI.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt
  have hformula := hCderiv.mul_const (f (p 1))
  have heq : (fun y => separatedProduct C f ![y, p 1]) = (fun y => C y * f (p 1)) := rfl
  change HasDerivAt (fun y => separatedProduct C f ![y, p 1])
    (coordPartial 0 (separatedProduct C f) p) (p 0) at hcurve
  rw [heq] at hcurve
  exact hcurve.unique hformula

theorem separatedProduct_partial_t {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (separatedProduct C f) p = C (p 0) * deriv f (p 1) := by
  have hd := (((separatedProduct_contDiffOn hC f hf).contDiffAt
    ((spatialStrip_isOpen hI).mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hd' : HasFDerivAt (separatedProduct C f) (fderiv ℝ (separatedProduct C f) p)
      (![p 0, p 1] : Coord) := by simpa only [point_eta] using hd
  have hcurve := hd'.comp_hasDerivAt (p 1) (verticalPoint_hasDerivAt (p 0) (p 1))
  have hformula := (hf.differentiable (by simp) (p 1)).hasDerivAt.const_mul (C (p 0))
  have heq : (fun y => separatedProduct C f ![p 0, y]) = (fun y => C (p 0) * f y) := rfl
  change HasDerivAt (fun y => separatedProduct C f ![p 0, y])
    (coordPartial 1 (separatedProduct C f) p) (p 1) at hcurve
  rw [heq] at hcurve
  exact hcurve.unique hformula

def taylorCorrection (C : ℝ → ℝ) (a : ℝ) (n : ℕ) : Coord → ℝ :=
  separatedProduct C (normalizedTimePower a (n + 2))

theorem taylorCorrection_contDiffOn {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (a : ℝ) (n : ℕ) :
    ContDiffOn ℝ ∞ (taylorCorrection C a n) (spatialStrip I) :=
  separatedProduct_contDiffOn hC _ (normalizedTimePower_contDiff a (n + 2))

theorem taylorCorrection_partial_x {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 0 (taylorCorrection C a n) p =
      separatedProduct (deriv C) (normalizedTimePower a (n + 2)) p :=
  separatedProduct_partial_x hC hI _ (normalizedTimePower_contDiff a (n + 2)) hp

theorem taylorCorrection_partial_t {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (n : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (taylorCorrection C a n) p =
      separatedProduct C (normalizedTimePower a (n + 1)) p := by
  rw [taylorCorrection, separatedProduct_partial_t hC hI _
    (normalizedTimePower_contDiff a (n + 2)) hp]
  rw [show n + 2 = (n + 1) + 1 by omega, normalizedTimePower_deriv]
  rfl

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Darboux_QStripJetControl
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem horizontal_partial_eq_of_slice_eq {f f0 : Coord → ℝ} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : ContDiffOn ℝ ∞ f0 U) (hU : IsOpen U)
    {left right a : ℝ}
    (hline : ∀ x ∈ Ioo left right, boxPoint x a ∈ U)
    (heq : ∀ x ∈ Ioo left right, f0 (boxPoint x a) = f (boxPoint x a))
    {x : ℝ} (hx : x ∈ Ioo left right) :
    coordPartial 0 f0 (boxPoint x a) = coordPartial 0 f (boxPoint x a) := by
  have hd : HasDerivAt (fun t => f (boxPoint t a)) (coordPartial 0 f (boxPoint x a)) x :=
    ((hf.contDiffAt (hU.mem_nhds (hline x hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt
      x (boxPoint_hasDerivAt_t x a)
  have hd0 : HasDerivAt (fun t => f0 (boxPoint t a)) (coordPartial 0 f0 (boxPoint x a)) x :=
    ((hf0.contDiffAt (hU.mem_nhds (hline x hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt
      x (boxPoint_hasDerivAt_t x a)
  have hev : (fun t => f0 (boxPoint t a)) =ᶠ[𝓝 x] (fun t => f (boxPoint t a)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    exact heq t ht
  rw [← hd0.deriv, ← hd.deriv]
  exact hev.deriv_eq

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Comparison_ComparisonSourceBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply
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

def pulseLeadingBound (a : ℝ) (ha : 0 < a) : ℝ :=
  axisBumpDerivativeBound a ha 0*axisBumpDerivativeBound (1/2) (by norm_num) 0/2

theorem pulseLeadingBound_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ pulseLeadingBound a ha := by
  exact div_nonneg (mul_nonneg (axisBumpDerivativeBound_pos ha 0).le
    (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ)<1/2) 0).le) (by norm_num)

theorem pulsePrincipalLeading_abs_bound {a tau : ℝ} (ha : 0 < a) (ht : 0 < tau)
    (N : ℕ) (delta : ℝ) (p : Coord) :
    |pulsePrincipalLeading a N delta tau p| ≤ pulseLeadingBound a ha*tau^2/tau^N := by
  let A0 := axisBumpDerivativeBound a ha 0
  let P0 := axisBumpDerivativeBound (1/2) (by norm_num) 0
  have hA0 : 0 ≤ A0 := (axisBumpDerivativeBound_pos ha 0).le
  have hP0 : 0 ≤ P0 := (axisBumpDerivativeBound_pos (by norm_num : (0 : ℝ)<1/2) 0).le
  have haxis : |axisBump a (p 0)| ≤ A0 := by
    simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using axisBump_derivative_le ha 0 (p 0)
  have htemp : |temporalCutoff (tau*p 1/delta)| ≤ P0 := by
    simpa only [temporalCutoff,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using
      axisBump_derivative_le (by norm_num : (0 : ℝ)<1/2) 0 (tau*p 1/delta)
  have hq : 0 ≤ tau^2/(2*tau^N) := by positivity
  calc
    _ = (tau^2/(2*tau^N))*|axisBump a (p 0)| *
        |temporalCutoff (tau*p 1/delta)| *|Real.cos (tau*p 0)| := by
      rw [pulsePrincipalLeading,abs_mul,abs_mul,abs_mul,abs_of_nonneg hq]
    _ ≤ (tau^2/(2*tau^N))*A0*P0*1 :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left haxis hq) htemp (abs_nonneg _)
        (mul_nonneg hq hA0)) (Real.abs_cos_le_one _) (abs_nonneg _)
        (mul_nonneg (mul_nonneg hq hA0) hP0)
    _ = _ := by dsimp [pulseLeadingBound,A0,P0]; field_simp [ht.ne']

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

theorem exists_rational_bounded_class_label (kappa : ℝ) (M : ℕ) (q : ℝ) :
    ∃ q0 : ℚ, |q - (q0 : ℝ)| < 1 / (100 * boundedClassWidth kappa M) := by
  let epsilon := 1 / (100 * boundedClassWidth kappa M)
  have hepsilon : 0 < epsilon := one_div_pos.mpr
    (mul_pos (by norm_num) (boundedClassWidth_pos kappa M))
  obtain ⟨q0, hlower, hupper⟩ := exists_rat_btwn
    (show q - epsilon < q + epsilon by linarith)
  refine ⟨q0, abs_lt.mpr ⟨?_, ?_⟩⟩ <;> linarith

end SmoothLocal.Perturbation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_NormalField
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open WithLp

namespace SmoothLocal.Geometry

def tangentCross (F : Coord → Ambient) (p : Coord) : Ambient :=
  ambientCross (coordPartial 0 F p) (coordPartial 1 F p)

def unitNormalField (F : Coord → Ambient) (p : Coord) : Ambient :=
  ‖tangentCross F p‖⁻¹ • tangentCross F p

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_RankOneOrientation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix BigOperators
open WithLp

namespace SmoothLocal.Geometry

def rotatedForm (H : Matrix (Fin 2) (Fin 2) ℝ) (a : PlanarAxis) :
    Matrix (Fin 2) (Fin 2) ℝ := (axisRotation a)ᵀ * H * axisRotation a

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_OrientedHeightPullback
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry
open SmoothLocal.Flow

def orientedCovHessian (g : MetricField) (z : Coord → ℝ)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  Rᵀ * covHessian g z p * R

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Pulses_QReferenceForcingMargins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Pulse

theorem actual_det_upper_of_entry_bound (g : MetricField) (p : Coord) {G : ℝ}
    (hG : 0 ≤ G) (hg : ∀ i j, |g p i j| ≤ G) : (g p).det ≤ 2*G^2 := by
  rw [Matrix.det_fin_two]
  calc
    g p 0 0*g p 1 1-g p 0 1*g p 1 0 ≤
        |g p 0 0*g p 1 1|+|g p 0 1*g p 1 0| := by
      linarith [le_abs_self (g p 0 0*g p 1 1),
        neg_le_abs (g p 0 1*g p 1 0)]
    _ = |g p 0 0| *|g p 1 1|+|g p 0 1| *|g p 1 0| := by rw [abs_mul,abs_mul]
    _ ≤ G*G+G*G := add_le_add
      (mul_le_mul (hg 0 0) (hg 1 1) (abs_nonneg _) hG)
      (mul_le_mul (hg 0 1) (hg 1 0) (abs_nonneg _) hG)
    _ = _ := by ring

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_FiniteTaylorComparison
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det
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

def linearCauchy (a : ℝ) (u0 u1 : ℝ → ℝ) (p : Coord) : ℝ :=
  u0 (p 0) + u1 (p 0) * (p 1 - a)

theorem linearCauchy_contDiffOn {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I) (a : ℝ) :
    ContDiffOn ℝ ∞ (linearCauchy a u0 u1) (spatialStrip I) :=
  (h0.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).add
    ((h1.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)).mul
      ((contDiffOn_apply ℝ ℝ 1 (spatialStrip I)).sub contDiffOn_const))

theorem linearCauchy_value (a x : ℝ) (u0 u1 : ℝ → ℝ) :
    linearCauchy a u0 u1 ![x, a] = u0 x := by simp [linearCauchy]

theorem linearCauchy_velocity {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I)
    (a : ℝ) {p : Coord} (hp : p ∈ spatialStrip I) :
    coordPartial 1 (linearCauchy a u0 u1) p = u1 (p 0) := by
  have hlin := linearCauchy_contDiffOn h0 h1 a
  have hd : HasFDerivAt (linearCauchy a u0 u1)
      (fderiv ℝ (linearCauchy a u0 u1) p) (![p 0, p 1] : Coord) := by
    simpa only [point_eta] using
      ((hlin.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hc := hd.comp_hasDerivAt (p 1) (verticalPoint_hasDerivAt (p 0) (p 1))
  have he : (fun t => linearCauchy a u0 u1 ![p 0, t]) =
      (fun t => u0 (p 0) + u1 (p 0) * (t - a)) := rfl
  change HasDerivAt (fun t => linearCauchy a u0 u1 ![p 0, t])
    (coordPartial 1 (linearCauchy a u0 u1) p) (p 1) at hc
  rw [he] at hc
  have hf := ((hasDerivAt_id (p 1)).sub_const a).const_mul (u1 (p 0))
  have hf' := hf.const_add (u0 (p 0))
  simpa only [mul_one] using hc.unique hf'

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorQJetBounds
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

theorem coordinateProjection_norm_le (i : Fin 2) :
    ‖(ContinuousLinearMap.proj i : Coord →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro p
  change ‖p i‖ ≤ 1 * ‖p‖
  rw [one_mul]
  exact norm_le_pi_norm p i

theorem coordinateProjection_positive_jet_bound (i : Fin 2) (p : Coord)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun q : Coord => q i) p‖ ≤ 1 := by
  let L : Coord →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h := L.norm_iteratedFDeriv_comp_left
    (f := fun q : Coord => q) (x := p) contDiffAt_id (n := n) (WithTop.coe_le_coe.mpr le_top)
  have hL : ‖L‖ ≤ 1 := coordinateProjection_norm_le i
  exact h.trans ((mul_le_mul hL (norm_iteratedFDeriv_id_pos p hn)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorCoefficientBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det
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

def initialAxisCLM : ℝ →L[ℝ] Coord :=
  ContinuousLinearMap.pi (fun i => if i = 0 then ContinuousLinearMap.id ℝ ℝ else 0)

theorem initialAxisCLM_eq (x : ℝ) : initialAxisCLM x = (![x, 0] : Coord) := by
  ext i
  fin_cases i <;> simp [initialAxisCLM]

theorem initialAxisCLM_norm_le : ‖initialAxisCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [one_mul, initialAxisCLM_eq]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro i
  fin_cases i
  · exact le_rfl
  · simp

theorem initialAxis_add (x a : ℝ) : initialAxisCLM x + (![0, a] : Coord) = ![x, a] := by
  rw [initialAxisCLM_eq]
  ext i
  fin_cases i <;> simp

theorem norm_initial_slice_jet_le {f : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hV : IsOpen V) (a x : ℝ)
    (hp : (![x, a] : Coord) ∈ V) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun y => f ![y, a]) x‖ ≤ ‖iteratedFDeriv ℝ k f ![x, a]‖ := by
  let shift : Coord → Coord := fun p => p + ![0, a]
  have hshift : ContDiff ℝ ∞ shift := contDiff_id.add contDiff_const
  have hpre : IsOpen (shift ⁻¹' V) := hV.preimage hshift.continuous
  have hfs : ContDiffOn ℝ ∞ (f ∘ shift) (shift ⁻¹' V) :=
    hf.comp hshift.contDiffOn (fun _ hp => hp)
  have hpoint : initialAxisCLM x ∈ shift ⁻¹' V := by
    change initialAxisCLM x + ![0, a] ∈ V
    rw [initialAxis_add]
    exact hp
  have hb := norm_iteratedFDeriv_comp_contraction initialAxisCLM hfs hpre
    initialAxisCLM_norm_le hpoint k
  have he : (f ∘ shift) ∘ initialAxisCLM = (fun y => f ![y, a]) := by
    funext y
    change f (initialAxisCLM y + ![0, a]) = f ![y, a]
    rw [initialAxis_add]
  rw [he] at hb
  change ‖iteratedFDeriv ℝ k (fun y => f ![y, a]) x‖ ≤
    ‖iteratedFDeriv ℝ k (fun p => f (p + ![0, a])) (initialAxisCLM x)‖ at hb
  rw [iteratedFDeriv_comp_add_right, initialAxis_add] at hb
  exact hb

end SmoothLocal.Taylor

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Taylor_TaylorPolynomialJetBounds
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det
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

theorem product_fullJet_bound {f h : Coord → ℝ} {V : Set Coord}
    (hf : ContDiffOn ℝ ∞ f V) (hh : ContDiffOn ℝ ∞ h V) (hV : IsOpen V)
    {p : Coord} (hp : p ∈ V) (k : ℕ) {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hfB : ∀ j ≤ k, ‖iteratedFDeriv ℝ j f p‖ ≤ A)
    (hhB : ∀ j ≤ k, ‖iteratedFDeriv ℝ j h p‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun q => f q * h q) p‖ ≤ (2 : ℝ)^k * A * B := by
  have hm := norm_iteratedFDerivWithin_mul_le hf hh hV.uniqueDiffOn hp
    (n := k) (WithTop.coe_le_coe.mpr le_top)
  simp_rw [iteratedFDerivWithin_of_isOpen _ hV hp] at hm
  have hsum : (∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ)) = (2 : ℝ)^k := by
    exact_mod_cast Nat.sum_range_choose k
  apply hm.trans
  calc
    _ ≤ ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * A * B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hfB j hjk) (Nat.cast_nonneg _))
        (hhB (k - j) (Nat.sub_le _ _)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (2 : ℝ)^k * A * B := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]

theorem spatialCoefficient_fullJet_le {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) {p : Coord} (hp : p 0 ∈ I) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : Coord => C (q 0)) p‖ ≤ ‖iteratedFDeriv ℝ k C (p 0)‖ := by
  have hh := norm_iteratedFDeriv_comp_contraction
    (ContinuousLinearMap.proj 0 : Coord →L[ℝ] ℝ) (f := C) hC hI
    (coordinateProjection_norm_le 0) (p := p) hp k
  change ‖iteratedFDeriv ℝ k (fun q : Coord => C (q 0)) p‖ ≤
    ‖iteratedFDeriv ℝ k C (p 0)‖ at hh
  exact hh

theorem timeMonomial_fullJet_le_one (a : ℝ) (m : ℕ) {p : Coord}
    (hp : |p 1 - a| ≤ 1) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : Coord => normalizedTimePower a m (q 1)) p‖ ≤ 1 := by
  have hh := norm_iteratedFDeriv_comp_contraction
    (ContinuousLinearMap.proj 1 : Coord →L[ℝ] ℝ) (f := normalizedTimePower a m)
    (normalizedTimePower_contDiff a m).contDiffOn isOpen_univ (coordinateProjection_norm_le 1)
      (p := p) (mem_univ (p 1)) k
  change ‖iteratedFDeriv ℝ k (fun q : Coord => normalizedTimePower a m (q 1)) p‖ ≤
    ‖iteratedFDeriv ℝ k (normalizedTimePower a m) (p 1)‖ at hh
  exact hh.trans (normalizedTimePower_fullJet_le_one a (p 1) m k hp)

theorem separatedTimePower_fullJet_bound {C : ℝ → ℝ} {I : Set ℝ}
    (hC : ContDiffOn ℝ ∞ C I) (hI : IsOpen I) (a : ℝ) (m k : ℕ)
    {p : Coord} (hp : p ∈ spatialStrip I) (ht : |p 1 - a| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B) (hCB : ∀ j ≤ k, ‖iteratedFDeriv ℝ j C (p 0)‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (separatedProduct C (normalizedTimePower a m)) p‖ ≤ (2 : ℝ)^k * B := by
  have hc : ContDiffOn ℝ ∞ (fun q : Coord => C (q 0)) (spatialStrip I) :=
    hC.comp (contDiffOn_apply ℝ ℝ 0 (spatialStrip I)) (fun _ hp => hp)
  have ht' : ContDiffOn ℝ ∞ (fun q : Coord => normalizedTimePower a m (q 1)) (spatialStrip I) :=
    ((normalizedTimePower_contDiff a m).comp (contDiff_apply ℝ ℝ 1)).contDiffOn
  have hb := product_fullJet_bound hc ht' (spatialStrip_isOpen hI) hp k hB zero_le_one
    (fun j hj => (spatialCoefficient_fullJet_le hC hI hp j).trans (hCB j hj))
    (fun order _ => timeMonomial_fullJet_le_one a m ht order)
  change ‖iteratedFDeriv ℝ k (separatedProduct C (normalizedTimePower a m)) p‖ ≤
    (2 : ℝ)^k * B * 1 at hb
  rw [mul_one] at hb
  exact hb

theorem linearCauchy_fullJet_bound {u0 u1 : ℝ → ℝ} {I : Set ℝ}
    (h0 : ContDiffOn ℝ ∞ u0 I) (h1 : ContDiffOn ℝ ∞ u1 I) (hI : IsOpen I)
    (a : ℝ) (k : ℕ) {p : Coord} (hp : p ∈ spatialStrip I) (ht : |p 1 - a| ≤ 1)
    {B : ℝ} (hB : 0 ≤ B)
    (h0B : ∀ j ≤ k, ‖iteratedFDeriv ℝ j u0 (p 0)‖ ≤ B)
    (h1B : ∀ j ≤ k, ‖iteratedFDeriv ℝ j u1 (p 0)‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (linearCauchy a u0 u1) p‖ ≤ (1 + (2 : ℝ)^k) * B := by
  have hf0 : ContDiffOn ℝ ∞ (fun q : Coord => u0 (q 0)) (spatialStrip I) :=
    h0.comp (contDiffOn_apply ℝ ℝ 0 _) (fun _ hp => hp)
  have hf1 := separatedProduct_contDiffOn h1 _ (normalizedTimePower_contDiff a 1)
  have he : linearCauchy a u0 u1 = (fun q => u0 (q 0)) +
      separatedProduct u1 (normalizedTimePower a 1) := by
    funext q
    simp [linearCauchy, separatedProduct, normalizedTimePower]
  rw [he, iteratedFDeriv_add_apply
    ((hf0.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top))
    ((hf1.contDiffAt ((spatialStrip_isOpen hI).mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top))]
  have hval := (norm_add_le _ _).trans (add_le_add
    ((spatialCoefficient_fullJet_le h0 hI hp k).trans (h0B k le_rfl))
    (separatedTimePower_fullJet_bound h1 hI a 1 k hp ht hB h1B))
  convert hval using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

end SmoothLocal.Taylor

end

end OAI
end


