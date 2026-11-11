-- Prove2me | Definitions.Def_Q226II003
-- name    : Q226II003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T17:38:38.489287+00:00
-- url     : https://prove2.me/theorems/cfcddd0c-be8e-4009-b11c-1e58cdb89646
-- title:
--   Definitions bundle Q226II003 of the split of OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SmoothLocal.Geometry.exists_local_metric_without_local_immersion`, carved from OpenAI's openai/math development (OpenAI, *A Smooth Metric with No Local Isometric Immersion into Three-Space*, OpenAI Math Release, September 24, 2026, result family 334, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 294 declarations of OpenAI's Lean: 53 definitions and 241 theorems. The definitions and types are `OAI.SmoothLocal.Flow.CapMetricJetBudget`, `OAI.SmoothLocal.Flow.FiniteCapMetricJets`, `OAI.SmoothLocal.Flow.Reflection.FiniteUpperCapMetricJets`, `OAI.SmoothLocal.Flow.Reflection.UpperCapRectangle.image`, `OAI.SmoothLocal.Flow.Reflection.UpperCapRectangle.lower`, `OAI.SmoothLocal.Flow.Reflection.UpperCapRectangle.region`, `OAI.SmoothLocal.Flow.Reflection.reflectPoint`, `OAI.SmoothLocal.Flow.Reflection.reflectedMetric`, `OAI.SmoothLocal.Flow.Reflection.reflectedScalar`, `OAI.SmoothLocal.Flow.Reflection.reflectedUpperRectangle`, `OAI.SmoothLocal.Flow.Reflection.reflectionIsometry`, `OAI.SmoothLocal.Flow.Reflection.upperCapPointwiseRequests`, `OAI.SmoothLocal.Flow.capChartRho`, `OAI.SmoothLocal.Flow.capPullback`, `OAI.SmoothLocal.Flow.flowField`, `OAI.SmoothLocal.Flow.lowerCapMetricRequests`, `OAI.SmoothLocal.Flow.lowerCapPointwiseRequests`, `OAI.SmoothLocal.Flow.originalC8L2Budget`, `OAI.SmoothLocal.Geometry.SmoothPositiveOn`, `OAI.SmoothLocal.Geometry.affineCoordinateHomeomorph`, `OAI.SmoothLocal.Geometry.affineInverseCoordinates`, `OAI.SmoothLocal.Geometry.affinePushforwardMetric`, `OAI.SmoothLocal.Geometry.bilinearMatrix`, `OAI.SmoothLocal.Geometry.christoffelFirstKind`, `OAI.SmoothLocal.Geometry.connectionHessianCorrection`, `OAI.SmoothLocal.Geometry.coordinateCovector`, `OAI.SmoothLocal.Geometry.loweredRiemann`, `OAI.SmoothLocal.Geometry.ordinaryCoordinateHessian`, `OAI.SmoothLocal.HighEquation.CoordinateL2Bound`, `OAI.SmoothLocal.Sobolev.regionSobolevEnergy`, `OAI.SmoothLocal.Weighted.capOuterSpatialCutoff`, `OAI.SmoothLocal.Weighted.capSpatialCutoff`, `OAI.SmoothLocal.Weighted.directedCoercivityDefect`, `OAI.SmoothLocal.Weighted.directedCutoffError`, `OAI.SmoothLocal.Weighted.directedGradientEnergy`, `OAI.SmoothLocal.Weighted.ellipticEdgeDerivativeConstant`, `OAI.SmoothLocal.Weighted.ellipticEnergy`, `OAI.SmoothLocal.Weighted.ellipticError`, `OAI.SmoothLocal.Weighted.ellipticErrorS`, `OAI.SmoothLocal.Weighted.ellipticErrorT` and 13 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `IsometricImmersion_Calculus_AffineCovariantHessian`, `IsometricImmersion_Calculus_AffineHessian`, `IsometricImmersion_Calculus_CoordinateJetNorm`, `IsometricImmersion_Calculus_FiniteUpperMetricJets`, `IsometricImmersion_Calculus_HessianCommutator`, `IsometricImmersion_Calculus_MixedCoordinateCalculus`, `IsometricImmersion_Calculus_NormedCoordinateCalculus`, `IsometricImmersion_Calculus_QuotientCalculus`, `IsometricImmersion_Caps_CapCutoffGeometry`, `IsometricImmersion_Caps_CapCutoffRectangle`, `IsometricImmersion_Caps_CapEllipticOverlap`, `IsometricImmersion_Caps_CapInductionData`, `IsometricImmersion_Caps_CapL2Basics`, `IsometricImmersion_Caps_CapOverlapCosts`, `IsometricImmersion_Caps_CapReflectionGeometry`, `IsometricImmersion_Caps_EllipticAbsorption`, `IsometricImmersion_Caps_EllipticApplication`, `IsometricImmersion_Caps_EllipticC1`, `IsometricImmersion_Caps_EllipticCutoff`, `IsometricImmersion_Caps_EllipticCutoffEdge`, `IsometricImmersion_Caps_EllipticEnergy`, `IsometricImmersion_Caps_EllipticGradient`, `IsometricImmersion_Caps_EllipticRatio`, `IsometricImmersion_Caps_FiniteCapInduction`, `IsometricImmersion_Caps_FiniteCapPointwise`, `IsometricImmersion_Caps_NestedCapRectangles`, `IsometricImmersion_Caps_UpperCapMetricJets`, `IsometricImmersion_Caps_UpperCapWords`, `IsometricImmersion_Caps_VaryingCapInduction`, `IsometricImmersion_Caps_VaryingMetricUpperCap`, `IsometricImmersion_Coordinates_AffinePullback`, `IsometricImmersion_Coordinates_AffinePushforward`, `IsometricImmersion_Curvature_AffineConnection`, `IsometricImmersion_Curvature_AffineCurvature`, `IsometricImmersion_Curvature_GaussConnection`, `IsometricImmersion_Curvature_IntrinsicCurvature`, `IsometricImmersion_Energy_DirectedCutoffBalance`, `IsometricImmersion_Energy_DirectedDefectCost`, `IsometricImmersion_Energy_DirectedEdgeDefect`, `IsometricImmersion_Energy_DirectedFluxCost`, `IsometricImmersion_Energy_DirectedIntegralEstimate`, `IsometricImmersion_Energy_DirectedWeightJetCost`, `IsometricImmersion_Energy_MultiplierDivergence`, `IsometricImmersion_Energy_MultiplierIntegral`, `IsometricImmersion_Energy_RectangleSobolev`, `IsometricImmersion_Energy_RectangleSobolevOne`, `IsometricImmersion_Energy_RegionSobolev`, `IsometricImmersion_Energy_WeightPrimitive`, `IsometricImmersion_Energy_WeightedMultiplier`, `IsometricImmersion_Flows_FlowCurvature`, `IsometricImmersion_Flows_FlowExistence`, `IsometricImmersion_Flows_FlowSobolev`, `IsometricImmersion_Flows_FlowTransport`, `IsometricImmersion_Immersions_InducedMetric`, `IsometricImmersion_Metric`, `IsometricImmersion_Metrics_MetricCompatibility`, `IsometricImmersion_Metrics_MetricLocality`, `IsometricImmersion_Metrics_MetricSmoothness`.
--
--   **Imports.** It imports the published bundle `Def_IsometricImmersion`; the bundles `Q226II000` and `Q226II001` of this split.
--
--   **Imported by** (directly, in this split): the bundles `Q226II007`, `Q226II008`, `Q226II009` and `Q226II010`.
-- source:
--   OpenAI, A Smooth Metric with No Local Isometric Immersion into Three-Space, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 334; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-Three-Space-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
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
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_IsometricImmersion
import Definitions.Def_Q226II000
import Definitions.Def_Q226II001

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

def SmoothPositiveOn (g : MetricField) (U : Set Coord) : Prop :=
  (∀ i j, ContDiffOn ℝ ∞ (fun p => g p i j) U) ∧ ∀ p ∈ U, (g p).PosDef

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Immersions_InducedMetric
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter
namespace SmoothLocal.Geometry

section Calculus
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F : Coord → V} {U : Set Coord} {p : Coord}

theorem second_coordPartial_eq_fderiv (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p =
      fderiv ℝ (fderiv ℝ F) p (Pi.single i 1) (Pi.single j 1) := by
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hs p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  unfold coordPartial
  rw [fderiv_clm_apply hd (differentiableAt_const (c := Pi.single j (1 : ℝ)))]
  simp

theorem coordPartial_comm (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (hp : p ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j F) p = coordPartial j (coordPartial i F) p := by
  rw [second_coordPartial_eq_fderiv hF hU hp, second_coordPartial_eq_fderiv hF hU hp]
  exact (((hF p hp).contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt
    (by
      simp only [minSmoothness, ite_eq_left (inferInstance : IsRCLikeNormedField ℝ)]
      exact WithTop.coe_le_coe.mpr le_top)) _ _

end Calculus

end SmoothLocal.Geometry

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

theorem affineCoordinates_contDiff (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ ∞ (affineCoordinates b R) :=
  contDiff_const.add (matrixContinuousLinear R).contDiff

theorem affineCoordinates_hasFDerivAt (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Coord) : HasFDerivAt (affineCoordinates b R) (matrixContinuousLinear R) q := by
  change HasFDerivAt (fun x => b + matrixContinuousLinear R x)
    (matrixContinuousLinear R) q
  exact (matrixContinuousLinear R).hasFDerivAt.const_add b

theorem affineCoordinates_fderiv (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (q : Coord) : fderiv ℝ (affineCoordinates b R) q = matrixContinuousLinear R :=
  (affineCoordinates_hasFDerivAt b R q).fderiv

theorem isOpen_affine_preimage {U : Set Coord} (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    IsOpen (affineCoordinates b R ⁻¹' U) :=
  hU.preimage (affineCoordinates_contDiff b R).continuous

theorem affine_comp_contDiffOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiffOn ℝ ∞ (f ∘ affineCoordinates b R) (affineCoordinates b R ⁻¹' U) :=
  hf.comp (affineCoordinates_contDiff b R).contDiffOn (fun _ hq => hq)

theorem fderiv_affine_comp_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q v : Coord)
    (hf : DifferentiableAt ℝ f (affineCoordinates b R q)) :
    fderiv ℝ (f ∘ affineCoordinates b R) q v =
      fderiv ℝ f (affineCoordinates b R q) (R *ᵥ v) := by
  rw [fderiv_comp q hf (affineCoordinates_hasFDerivAt b R q).differentiableAt,
    affineCoordinates_fderiv, ContinuousLinearMap.comp_apply, matrixContinuousLinear_apply]

theorem matrix_pullback_bilinear (G R : Matrix (Fin 2) (Fin 2) ℝ) (v w : Coord) :
    (R *ᵥ v) ⬝ᵥ (G *ᵥ (R *ᵥ w)) = v ⬝ᵥ ((Rᵀ * G * R) *ᵥ w) := by
  calc
    _ = (G *ᵥ (R *ᵥ w)) ⬝ᵥ (R *ᵥ v) := dotProduct_comm _ _
    _ = v ⬝ᵥ (Rᵀ *ᵥ (G *ᵥ (R *ᵥ w))) :=
      (Matrix.dotProduct_transpose_mulVec R v (G *ᵥ (R *ᵥ w))).symm
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem affinePullbackMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : Function.Injective R.mulVec) :
    SmoothPositiveOn (affinePullbackMetric g b R) (affineCoordinates b R ⁻¹' U) := by
  constructor
  · intro i j
    have hc (a k : Fin 2) : ContDiffOn ℝ ∞
        (fun q => g (affineCoordinates b R q) a k) (affineCoordinates b R ⁻¹' U) :=
      affine_comp_contDiffOn (hg.1 a k) b R
    simp only [affinePullbackMetric, Matrix.mul_apply, Matrix.transpose_apply]
    apply ContDiffOn.sum
    intro k _
    apply ContDiffOn.mul _ contDiffOn_const
    apply ContDiffOn.sum
    intro a _
    exact contDiffOn_const.mul (hc a k)
  · intro q hq
    simpa only [affinePullbackMetric, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hg.2 (affineCoordinates b R q) hq).conjTranspose_mul_mul_same hR

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_AffineHessian
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

def bilinearMatrix (B : Coord →L[ℝ] Coord →L[ℝ] ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a k => B (Pi.single a 1) (Pi.single k 1)

theorem bilinear_matrix_congruence (B : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    B (R *ᵥ Pi.single i 1) (R *ᵥ Pi.single j 1) =
      (Rᵀ * bilinearMatrix B * R) i j := by
  rw [matrix_column_basis_expansion R i, matrix_column_basis_expansion R j]
  simp only [map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, bilinearMatrix]
  ring

theorem second_coordPartial_affine_comp {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) (i j : Fin 2) :
    coordPartial i (coordPartial j (z ∘ affineCoordinates b R)) q =
      fderiv ℝ (fderiv ℝ z) (affineCoordinates b R q)
        (R *ᵥ Pi.single i 1) (R *ᵥ Pi.single j 1) := by
  have hV := isOpen_affine_preimage hU b R
  have heq : coordPartial j (z ∘ affineCoordinates b R) =ᶠ[𝓝 q]
      (fun p => fderiv ℝ z (affineCoordinates b R p) (R *ᵥ Pi.single j 1)) := by
    filter_upwards [hV.mem_nhds hq] with p hp
    exact fderiv_affine_comp_apply b R p (Pi.single j 1)
      (((hz _ hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hs : ContDiffOn ℝ ∞ (fderiv ℝ z) U := hz.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd : DifferentiableAt ℝ (fderiv ℝ z) (affineCoordinates b R q) :=
    (((hs _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hdc : DifferentiableAt ℝ
      (fun p => fderiv ℝ z (affineCoordinates b R p)) q :=
    hd.comp q (affineCoordinates_hasFDerivAt b R q).differentiableAt
  have heval : coordPartial i (coordPartial j (z ∘ affineCoordinates b R)) q =
      fderiv ℝ (fun p => fderiv ℝ z (affineCoordinates b R p)) q
        (Pi.single i 1) (R *ᵥ Pi.single j 1) := by
    change fderiv ℝ (coordPartial j (z ∘ affineCoordinates b R)) q (Pi.single i 1) = _
    rw [heq.fderiv_eq, fderiv_clm_apply hdc
      (differentiableAt_const (c := R *ᵥ Pi.single j (1 : ℝ)))]
    simp
  rw [heval]
  exact congrArg (fun L : Coord →L[ℝ] ℝ => L (R *ᵥ Pi.single j 1))
    (fderiv_affine_comp_apply b R q (Pi.single i 1) hd)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricSmoothness
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix

namespace SmoothLocal.Geometry

variable {g : MetricField} {U : Set Coord}

theorem metricDet_ne_zero (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) :
    (g p).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit).ne_zero

theorem metricDet_contDiffOn (hg : SmoothPositiveOn g U) :
    ContDiffOn ℝ ∞ (fun p => (g p).det) U := by
  simpa only [Matrix.det_fin_two] using
    ((hg.1 0 0).mul (hg.1 1 1)).sub ((hg.1 0 1).mul (hg.1 1 0))

theorem metricAdjugate_contDiffOn (hg : SmoothPositiveOn g U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => (g p).adjugate i j) U := by
  fin_cases i <;> fin_cases j
  · simpa [Matrix.adjugate_fin_two] using hg.1 1 1
  · simpa [Matrix.adjugate_fin_two] using (hg.1 0 1).neg
  · simpa [Matrix.adjugate_fin_two] using (hg.1 1 0).neg
  · simpa [Matrix.adjugate_fin_two] using hg.1 0 0

theorem inverseMetric_contDiffOn (hg : SmoothPositiveOn g U) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun p => inverseMetric g p i j) U := by
  have hi : ContDiffOn ℝ ∞ (fun p => ((g p).det)⁻¹) U :=
    (metricDet_contDiffOn hg).inv (fun p hp => metricDet_ne_zero hg hp)
  have ha := metricAdjugate_contDiffOn hg i j
  simpa [inverseMetric, Matrix.inv_def, Ring.inverse_eq_inv, smul_eq_mul] using hi.mul ha

theorem christoffel_contDiffOn (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (k i j : Fin 2) :
    ContDiffOn ℝ ∞ (christoffel g k i j) U := by
  have hs : ContDiffOn ℝ ∞ (fun p => ∑ l, inverseMetric g p k l *
      (coordPartial i (fun q => g q j l) p +
        coordPartial j (fun q => g q i l) p -
        coordPartial l (fun q => g q i j) p)) U := by
    apply ContDiffOn.sum
    intro l hl
    exact (inverseMetric_contDiffOn hg k l).mul
      (((partial_contDiffOn (hg.1 j l) hU i).add
        (partial_contDiffOn (hg.1 i l) hU j)).sub
        (partial_contDiffOn (hg.1 i j) hU l))
  exact contDiffOn_const.mul hs

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_HessianCommutator
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace HessianCalculus

variable {f h : Coord → ℝ} {p : Coord}

theorem coordPartial_add_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q + h q) p = coordPartial i f p + coordPartial i h p := by
  simp [coordPartial, fderiv_fun_add hf hh]

theorem coordPartial_mul_at
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p) (i : Fin 2) :
    coordPartial i (fun q => f q * h q) p =
      coordPartial i f p * h p + f p * coordPartial i h p := by
  simp [coordPartial, fderiv_fun_mul hf hh, add_comm, mul_comm]

theorem coordPartial_sum_two (f : Fin 2 → Coord → ℝ)
    (hf : ∀ a, DifferentiableAt ℝ (f a) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, f a q) p = ∑ a, coordPartial i (f a) p := by
  simp only [Fin.sum_univ_two]
  exact coordPartial_add_at (hf 0) (hf 1) i

end HessianCalculus

variable {g : MetricField} {z : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem metric_coeff_symm (hg : SmoothPositiveOn g U) (hp : p ∈ U) (i j : Fin 2) :
    g p i j = g p j i := by
  simpa using (hg.2 p hp).1.apply j i

theorem metric_coeff_partial_symm (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    coordPartial k (fun q => g q i j) p = coordPartial k (fun q => g q j i) p := by
  have heq : (fun q => g q i j) =ᶠ[𝓝 p] (fun q => g q j i) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact metric_coeff_symm hg hq i j
  unfold coordPartial
  rw [heq.fderiv_eq]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_GaussConnection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff BigOperators Matrix
namespace SmoothLocal.Geometry

def christoffelFirstKind (g : MetricField) (i j : Fin 2) (p : Coord) : Coord :=
  fun l => (coordPartial i (fun q => g q j l) p +
    coordPartial j (fun q => g q i l) p - coordPartial l (fun q => g q i j) p) / 2

theorem christoffel_eq_inverse_mulVec (g : MetricField) (i j : Fin 2) (p : Coord) :
    (fun k => christoffel g k i j p) = (g p)⁻¹ *ᵥ christoffelFirstKind g i j p := by
  ext k
  simp only [christoffel, inverseMetric, Matrix.mulVec, dotProduct, christoffelFirstKind]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem metric_mul_christoffel {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) {p : Coord} (hp : p ∈ U) (i j : Fin 2) :
    g p *ᵥ (fun k => christoffel g k i j p) = christoffelFirstKind g i j p := by
  rw [christoffel_eq_inverse_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hg.2 p hp).isUnit),
    Matrix.one_mulVec]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Metrics_MetricCompatibility
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

theorem metric_compatibility (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (k i j : Fin 2) :
    coordPartial k (fun q => g q i j) p =
      (∑ r, christoffel g r k i p * g p r j) +
        (∑ r, christoffel g r k j p * g p i r) := by
  have hlower (a b c : Fin 2) :
      (∑ r, christoffel g r a b p * g p c r) = christoffelFirstKind g a b p c := by
    simpa only [Matrix.mulVec, dotProduct, mul_comm] using
      congrFun (metric_mul_christoffel hg hp a b) c
  have hsym : (∑ r, christoffel g r k i p * g p r j) =
      ∑ r, christoffel g r k i p * g p j r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [metric_coeff_symm hg hp r j]
  rw [hsym, hlower k i j, hlower k j i]
  simp only [christoffelFirstKind]
  rw [metric_coeff_partial_symm hg hU hp k j i]
  ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_IntrinsicCurvature
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem metric_second_compatibility (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (d k i j : Fin 2) :
    coordPartial d (coordPartial k (fun q => g q i j)) p =
      (∑ r, (coordPartial d (christoffel g r k i) p * g p r j +
        christoffel g r k i p * coordPartial d (fun q => g q r j) p)) +
      (∑ r, (coordPartial d (christoffel g r k j) p * g p i r +
        christoffel g r k j p * coordPartial d (fun q => g q i r) p)) := by
  have heq : coordPartial k (fun q => g q i j) =ᶠ[𝓝 p]
      (fun q => (∑ r, christoffel g r k i q * g q r j) +
        (∑ r, christoffel g r k j q * g q i r)) := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact metric_compatibility hg hU hq k i j
  have hdg (a b : Fin 2) : DifferentiableAt ℝ (fun q => g q a b) p :=
    (((hg.1 a b) p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdΓ (a b c : Fin 2) : DifferentiableAt ℝ (christoffel g a b c) p :=
    (((christoffel_contDiffOn hg hU a b c) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hA (r : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g r k i q * g q r j) p := (hdΓ r k i).mul (hdg r j)
  have hB (r : Fin 2) : DifferentiableAt ℝ
      (fun q => christoffel g r k j q * g q i r) p := (hdΓ r k j).mul (hdg i r)
  change fderiv ℝ (coordPartial k (fun q => g q i j)) p (Pi.single d 1) = _
  rw [heq.fderiv_eq]
  change coordPartial d (fun q => (∑ r, christoffel g r k i q * g q r j) +
    (∑ r, christoffel g r k j q * g q i r)) p = _
  rw [HessianCalculus.coordPartial_add_at
      (DifferentiableAt.fun_sum fun r _ => hA r)
      (DifferentiableAt.fun_sum fun r _ => hB r) d,
    HessianCalculus.coordPartial_sum_two _ hA d,
    HessianCalculus.coordPartial_sum_two _ hB d]
  congr 1
  · apply Finset.sum_congr rfl
    intro r _
    exact HessianCalculus.coordPartial_mul_at (hdΓ r k i) (hdg r j) d
  · apply Finset.sum_congr rfl
    intro r _
    exact HessianCalculus.coordPartial_mul_at (hdΓ r k j) (hdg i r) d

def loweredRiemann (g : MetricField) (l k i j : Fin 2) (p : Coord) : ℝ :=
  ∑ r, g p l r * riemann g r k i j p

theorem loweredRiemann_skew_last (g : MetricField) (l k i j : Fin 2) (p : Coord) :
    loweredRiemann g l k i j p = -loweredRiemann g l k j i p := by
  simp only [loweredRiemann, riemann, Fin.sum_univ_two]
  ring

theorem loweredRiemann_skew_first_add (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    loweredRiemann g l k i j p + loweredRiemann g k l i j p = 0 := by
  have hc := coordPartial_comm (hg.1 k l) hU hp i j
  rw [metric_second_compatibility hg hU hp i j k l,
    metric_second_compatibility hg hU hp j i k l] at hc
  simp only [metric_compatibility hg hU hp, Fin.sum_univ_two] at hc
  simp only [loweredRiemann, riemann, Fin.sum_univ_two]
  simp only [metric_coeff_symm hg hp] at hc ⊢
  linear_combination hc

theorem loweredRiemann_skew_first (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    loweredRiemann g l k i j p = -loweredRiemann g k l i j p := by
  have h := loweredRiemann_skew_first_add hg hU hp l k i j
  linarith

theorem loweredRiemann_self_first (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l i j : Fin 2) : loweredRiemann g l l i j p = 0 := by
  have h := loweredRiemann_skew_first_add hg hU hp l l i j
  linarith

theorem loweredRiemann_self_last (g : MetricField) (l k i : Fin 2) (p : Coord) :
    loweredRiemann g l k i i p = 0 := by
  have h := loweredRiemann_skew_last g l k i i p
  linarith

theorem loweredRiemann_0101 (hg : SmoothPositiveOn g U) (hp : p ∈ U) :
    loweredRiemann g 0 1 0 1 p = gaussianCurvature g p * (g p).det := by
  unfold loweredRiemann gaussianCurvature
  rw [div_mul_cancel₀ _ (metricDet_ne_zero hg hp)]

theorem loweredRiemann_factorization (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hp : p ∈ U) (l k i j : Fin 2) :
    loweredRiemann g l k i j p = gaussianCurvature g p *
      (g p l i * g p j k - g p l j * g p i k) := by
  have h10 (a b : Fin 2) : loweredRiemann g 1 0 a b p = -loweredRiemann g 0 1 a b p :=
    loweredRiemann_skew_first hg hU hp 1 0 a b
  have hrev : loweredRiemann g 0 1 1 0 p = -loweredRiemann g 0 1 0 1 p :=
    loweredRiemann_skew_last g 0 1 1 0 p
  have hsym : g p 1 0 = g p 0 1 := metric_coeff_symm hg hp 1 0
  fin_cases l <;> fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp only [Fin.mk_zero, Fin.mk_one, loweredRiemann_self_first hg hU hp, loweredRiemann_self_last,
      h10, hrev, loweredRiemann_0101 hg hp, Matrix.det_fin_two, hsym] <;> ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_AffineConnection
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace AffineCalculus

theorem coordPartial_const_mul_at {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 2) :
    coordPartial i (fun q => c * f q) p = c * coordPartial i f p := by
  simp [coordPartial, fderiv_const_mul hf]

theorem coordPartial_mul_const_at {f : Coord → ℝ} {p : Coord}
    (hf : DifferentiableAt ℝ f p) (c : ℝ) (i : Fin 2) :
    coordPartial i (fun q => f q * c) p = coordPartial i f p * c := by
  simpa only [mul_comm] using coordPartial_const_mul_at hf c i

end AffineCalculus

theorem coordPartial_affine_comp {f : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hf : DifferentiableAt ℝ f (affineCoordinates b R q)) (i : Fin 2) :
    coordPartial i (f ∘ affineCoordinates b R) q =
      ∑ a, R a i * coordPartial a f (affineCoordinates b R q) := by
  change fderiv ℝ (f ∘ affineCoordinates b R) q (Pi.single i 1) = _
  rw [fderiv_affine_comp_apply b R q (Pi.single i 1) hf,
    matrix_column_basis_expansion R i]
  simp only [map_add, map_smul, smul_eq_mul, Fin.sum_univ_two, coordPartial]

theorem coordPartial_affinePullbackMetric {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) (k i j : Fin 2) :
    coordPartial k (fun p => affinePullbackMetric g b R p i j) q =
      ∑ a, ∑ c, ∑ d, R a i * R c j * R d k *
        coordPartial d (fun p => g p a c) (affineCoordinates b R q) := by
  have hd (a c : Fin 2) : DifferentiableAt ℝ (fun p => g p a c)
      (affineCoordinates b R q) :=
    (((hg.1 a c) _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdc (a c : Fin 2) : DifferentiableAt ℝ
      (fun p => g (affineCoordinates b R p) a c) q :=
    (hd a c).comp q (affineCoordinates_hasFDerivAt b R q).differentiableAt
  have hs (c : Fin 2) : DifferentiableAt ℝ
      (fun p => ∑ a, R a i * g (affineCoordinates b R p) a c) q :=
    DifferentiableAt.fun_sum fun a _ => (hdc a c).const_mul (R a i)
  have hchain (a c : Fin 2) :
      coordPartial k (fun p => g (affineCoordinates b R p) a c) q =
        ∑ d, R d k * coordPartial d (fun p => g p a c) (affineCoordinates b R q) :=
    coordPartial_affine_comp b R q (hd a c) k
  simp only [affinePullbackMetric, Matrix.mul_apply, Matrix.transpose_apply]
  rw [HessianCalculus.coordPartial_sum_two _
    (fun c => (hs c).mul_const (R c j)) k]
  simp_rw [AffineCalculus.coordPartial_mul_const_at (hs _) _ k,
    HessianCalculus.coordPartial_sum_two _
      (fun a => (hdc a _).const_mul (R a i)) k,
    AffineCalculus.coordPartial_const_mul_at (hdc _ _) _ k,
    hchain]
  simp only [Fin.sum_univ_two]
  ring

theorem christoffelFirstKind_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) (i j l : Fin 2) :
    christoffelFirstKind (affinePullbackMetric g b R) i j q l =
      ∑ a, ∑ c, ∑ d, R a l * R c i * R d j *
        christoffelFirstKind g c d (affineCoordinates b R q) a := by
  simp only [christoffelFirstKind, coordPartial_affinePullbackMetric hg hU b R q hq,
    Fin.sum_univ_two]
  ring

theorem christoffel_affinePullback_push {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a i j : Fin 2) :
    (∑ l, R a l * christoffel (affinePullbackMetric g b R) l i j q) =
      ∑ c, ∑ d, R c i * R d j * christoffel g a c d (affineCoordinates b R q) := by
  have hRinj : Function.Injective R.mulVec := Matrix.mulVec_injective_of_isUnit hR
  have hgR := affinePullbackMetric_smoothPositive hg b R hRinj
  have hRt : IsUnit Rᵀ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det _).mp hR
  have hlower (l c d : Fin 2) :
      christoffelFirstKind g c d (affineCoordinates b R q) l =
        ∑ r, g (affineCoordinates b R q) l r *
          christoffel g r c d (affineCoordinates b R q) :=
    (congrFun (metric_mul_christoffel hg hq c d) l).symm
  have heq :
      (Rᵀ * g (affineCoordinates b R q)) *ᵥ
        (R *ᵥ (fun l => christoffel (affinePullbackMetric g b R) l i j q)) =
      (Rᵀ * g (affineCoordinates b R q)) *ᵥ
        (fun r => ∑ c, ∑ d, R c i * R d j *
          christoffel g r c d (affineCoordinates b R q)) := by
    rw [Matrix.mulVec_mulVec]
    change affinePullbackMetric g b R q *ᵥ
      (fun l => christoffel (affinePullbackMetric g b R) l i j q) = _
    rw [metric_mul_christoffel hgR hq i j]
    ext l
    rw [christoffelFirstKind_affinePullback hg hU b R q hq]
    simp only [hlower, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
      dotProduct, Fin.sum_univ_two]
    ring
  have hv := Matrix.mulVec_injective_of_isUnit
    (hRt.mul (hg.2 (affineCoordinates b R q) hq).isUnit) heq
  exact congrFun hv a

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_AffineCovariantHessian
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def ordinaryCoordinateHessian (z : Coord → ℝ) (p : Coord) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => coordPartial i (coordPartial j z) p

def connectionHessianCorrection (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  ∑ k, christoffel g k i j p * coordPartial k z p

theorem covHessian_eq_ordinary_sub_correction (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    covHessian g z p = ordinaryCoordinateHessian z p - connectionHessianCorrection g z p := rfl

theorem ordinaryCoordinateHessian_affine_comp {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hq : affineCoordinates b R q ∈ U) :
    ordinaryCoordinateHessian (z ∘ affineCoordinates b R) q =
      Rᵀ * ordinaryCoordinateHessian z (affineCoordinates b R q) * R := by
  have hB : ordinaryCoordinateHessian z (affineCoordinates b R q) =
      bilinearMatrix (fderiv ℝ (fderiv ℝ z) (affineCoordinates b R q)) := by
    ext i j
    exact second_coordPartial_eq_fderiv hz hU hq i j
  rw [hB]
  ext i j
  change coordPartial i (coordPartial j (z ∘ affineCoordinates b R)) q = _
  rw [second_coordPartial_affine_comp hz hU b R q hq i j]
  exact bilinear_matrix_congruence (fderiv ℝ (fderiv ℝ z) (affineCoordinates b R q)) R i j

theorem connectionHessianCorrection_affine_comp
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) :
    connectionHessianCorrection (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      Rᵀ * connectionHessianCorrection g z (affineCoordinates b R q) * R := by
  have hdz : DifferentiableAt ℝ z (affineCoordinates b R q) :=
    (((hz _ hq).contDiffAt (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hchain (k : Fin 2) : coordPartial k (z ∘ affineCoordinates b R) q =
      ∑ a, R a k * coordPartial a z (affineCoordinates b R q) :=
    coordPartial_affine_comp b R q hdz k
  ext i j
  change (∑ k, christoffel (affinePullbackMetric g b R) k i j q *
    coordPartial k (z ∘ affineCoordinates b R) q) = _
  simp only [hchain]
  calc
    _ = ∑ a, coordPartial a z (affineCoordinates b R q) *
        (∑ k, R a k * christoffel (affinePullbackMetric g b R) k i j q) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = ∑ a, coordPartial a z (affineCoordinates b R q) *
        (∑ c, ∑ d, R c i * R d j * christoffel g a c d (affineCoordinates b R q)) := by
      simp_rw [christoffel_affinePullback_push hg hU b R hR q hq]
    _ = _ := by
      simp only [connectionHessianCorrection, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two]
      ring

theorem covHessian_affinePullback
    {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) :
    covHessian (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      Rᵀ * covHessian g z (affineCoordinates b R q) * R := by
  rw [covHessian_eq_ordinary_sub_correction, covHessian_eq_ordinary_sub_correction,
    ordinaryCoordinateHessian_affine_comp hz hU b R q hq,
    connectionHessianCorrection_affine_comp hg hz hU b R hR q hq]
  simp only [Matrix.mul_sub, Matrix.sub_mul]

def coordinateCovector (z : Coord → ℝ) (p : Coord) : Coord := fun i => coordPartial i z p

theorem coordinateCovector_affine_comp {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord)
    (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    coordinateCovector (z ∘ affineCoordinates b R) q =
      Rᵀ *ᵥ coordinateCovector z (affineCoordinates b R q) := by
  ext i
  exact coordPartial_affine_comp b R q hz i

theorem covectorNormSq_eq_dotProduct (g : MetricField) (z : Coord → ℝ) (p : Coord) :
    covectorNormSq g z p = coordinateCovector z p ⬝ᵥ
      (inverseMetric g p *ᵥ coordinateCovector z p) := by
  simp only [covectorNormSq, coordinateCovector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem inverseMetric_affinePullback (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord) :
    inverseMetric (affinePullbackMetric g b R) q =
      R⁻¹ * inverseMetric g (affineCoordinates b R q) * R⁻¹ᵀ := by
  simp only [inverseMetric, affinePullbackMetric, Matrix.mul_inv_rev,
    ← Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem covectorNormSq_affinePullback {g : MetricField} {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    covectorNormSq (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      covectorNormSq g z (affineCoordinates b R q) := by
  have hRS := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  have hT : R⁻¹ᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
  let v := coordinateCovector z (affineCoordinates b R q)
  have hvec : R⁻¹ᵀ *ᵥ (Rᵀ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  have hquad := matrix_pullback_bilinear (inverseMetric g (affineCoordinates b R q))
    R⁻¹ᵀ (Rᵀ *ᵥ v) (Rᵀ *ᵥ v)
  simp only [hvec, Matrix.transpose_transpose] at hquad
  rw [covectorNormSq_eq_dotProduct, covectorNormSq_eq_dotProduct,
    coordinateCovector_affine_comp b R q hz, inverseMetric_affinePullback]
  exact hquad.symm

theorem heightEnergy_affinePullback {g : MetricField} {z : Coord → ℝ}
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hz : DifferentiableAt ℝ z (affineCoordinates b R q)) :
    heightEnergy (affinePullbackMetric g b R) (z ∘ affineCoordinates b R) q =
      R.det ^ 2 * heightEnergy g z (affineCoordinates b R q) := by
  rw [heightEnergy, covectorNormSq_affinePullback b R hR q hz]
  simp only [affinePullbackMetric, Matrix.det_mul, Matrix.det_transpose, heightEnergy]
  ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_QuotientCalculus
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

variable {f h : Coord → ℝ} {p : Coord} {U : Set Coord}

theorem coordPartial_div
    (hf : DifferentiableAt ℝ f p) (hh : DifferentiableAt ℝ h p)
    (hne : h p ≠ 0) (i : Fin 2) :
    coordPartial i (fun x => f x / h x) p =
      (coordPartial i f p * h p - f p * coordPartial i h p) / (h p) ^ 2 := by
  have hinv : HasFDerivAt (fun x : Coord => (h x)⁻¹)
      (-(h p ^ 2)⁻¹ • fderiv ℝ h p) p := by
    simpa only [Function.comp_def] using
      (hasDerivAt_inv hne).comp_hasFDerivAt p hh.hasFDerivAt
  have hquot : HasFDerivAt (fun x : Coord => f x / h x)
      (f p • (-(h p ^ 2)⁻¹ • fderiv ℝ h p) +
        (h p)⁻¹ • fderiv ℝ f p) p := by
    simpa only [div_eq_mul_inv] using hf.hasFDerivAt.fun_mul hinv
  unfold coordPartial
  rw [hquot.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp [hne]
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

theorem coordPartial_eq_of_eventuallyEq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f h : Coord → V} {p : Coord} (heq : f =ᶠ[𝓝 p] h) (i : Fin 2) :
    coordPartial i f p = coordPartial i h p := by
  unfold coordPartial
  rw [heq.fderiv_eq]

theorem metric_coeff_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (i j : Fin 2) :
    (fun q => g q i j) =ᶠ[𝓝 p] (fun q => h q i j) :=
  heq.mono fun _ hq => congrFun (congrFun hq i) j

theorem christoffel_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (k i j : Fin 2) :
    christoffel g k i j p = christoffel h k i j p := by
  have hval := heq.self_of_nhds
  have hd (a b c : Fin 2) : coordPartial a (fun q => g q b c) p =
      coordPartial a (fun q => h q b c) p :=
    coordPartial_eq_of_eventuallyEq (metric_coeff_eventuallyEq heq b c) a
  simp only [christoffel, inverseMetric, hval, hd]

theorem christoffel_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (k i j : Fin 2) :
    christoffel g k i j =ᶠ[𝓝 p] christoffel h k i j :=
  heq.eventuallyEq_nhds.mono fun _ hq => christoffel_eq_of_eventuallyEq hq k i j

theorem riemann_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) (l k i j : Fin 2) :
    riemann g l k i j p = riemann h l k i j p := by
  have hΓ := christoffel_eq_of_eventuallyEq heq
  have hd (a b c d : Fin 2) : coordPartial a (christoffel g b c d) p =
      coordPartial a (christoffel h b c d) p :=
    coordPartial_eq_of_eventuallyEq (christoffel_eventuallyEq heq b c d) a
  simp only [riemann, hΓ, hd]

theorem gaussianCurvature_eq_of_eventuallyEq {g h : MetricField} {p : Coord}
    (heq : g =ᶠ[𝓝 p] h) : gaussianCurvature g p = gaussianCurvature h p := by
  simp only [gaussianCurvature, heq.self_of_nhds, riemann_eq_of_eventuallyEq heq]

theorem metric_add_eventuallyEq_of_not_mem_tsupport (g η : MetricField)
    {p : Coord} (hp : p ∉ tsupport η) : g + η =ᶠ[𝓝 p] g := by
  filter_upwards [eventuallyEq_zero_of_not_mem_tsupport η hp] with q hq
  change g q + η q = g q
  simp only [hq, Pi.zero_apply, add_zero]

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_CoordinateJetNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Geometry

theorem iteratedCoordPartial_eq_jet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ds : List (Fin 2))
    {p : Coord} (hp : p ∈ U) :
    iteratedCoordPartial ds f p = iteratedFDeriv ℝ ds.length f p (coordinateDirections ds) := by
  induction ds generalizing p with
  | nil => rfl
  | cons i ds ih =>
    have he : iteratedCoordPartial ds f =ᶠ[𝓝 p]
        (fun x => iteratedFDeriv ℝ ds.length f x (coordinateDirections ds)) := by
      filter_upwards [hU.mem_nhds hp] with x hx
      exact ih hx
    change coordPartial i (iteratedCoordPartial ds f) p = _
    rw [coordPartial_eq_of_eventuallyEq he i]
    have hd := (hf.contDiffAt (hU.mem_nhds hp)).differentiableAt_iteratedFDeriv
      (ENat.natCast_lt_of_coe_top_le_withTop le_rfl ds.length)
    simp only [List.length_cons]
    rw [hd.iteratedFDeriv_succ_apply_left']
    rfl

theorem norm_iteratedCoordPartial_le_jet
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ds : List (Fin 2))
    {p : Coord} (hp : p ∈ U) :
    ‖iteratedCoordPartial ds f p‖ ≤ ‖iteratedFDeriv ℝ ds.length f p‖ := by
  rw [iteratedCoordPartial_eq_jet hf hU ds hp]
  simpa only [coordinateDirections_norm, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ ds.length f p).le_opNorm (coordinateDirections ds)

theorem coordinateBound_of_frechet_bounds {f : Coord → ℝ} {U S : Set Coord} {n : ℕ} {M : ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hSU : S ⊆ U)
    (hB : ∀ k ≤ n, ∀ p ∈ S, ‖iteratedFDeriv ℝ k f p‖ ≤ M) :
    CoordinateBound f S n M := by
  intro ds hds p hp
  exact (norm_iteratedCoordPartial_le_jet hf hU ds (hSU hp)).trans (hB ds.length hds p hp)

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_WeightedMultiplier
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def multiplierT (B m n : Coord → ℝ) (p : Coord) : ℝ :=
  (coordPartial 1 m p - coordPartial 0 n p) / 2 + B p * n p

def multiplierS (A C m n : Coord → ℝ) (p : Coord) : ℝ :=
  -coordPartial 1 (fun q => A q * m q) p / 2 +
    coordPartial 0 (fun q => A q * n q) p / 2 + C p * m p

def multiplierJ (A B C m n : Coord → ℝ) (p : Coord) : ℝ :=
  -coordPartial 0 m p + B p * m p -
    coordPartial 1 (fun q => A q * n q) p + C p * n p

variable {I : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem directedWeight_partial
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (i : Fin 2) :
    coordPartial i (directedWeight b lambda I) p =
      -8 * (edgeDistance b p) ^ 7 * (if (1 : Fin 2) = i then 1 else 0) *
          Real.exp (weightPhase lambda I p) +
        directedWeight b lambda I p *
          (coordPartial i I p - lambda * (if (1 : Fin 2) = i then 1 else 0)) := by
  have hD := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hPhi := ((hasFDerivAt_apply (𝕜 := ℝ) 1 p).const_mul (-lambda)).add hI.hasFDerivAt
  have hd := (hD.pow 8).fun_mul hPhi.exp
  simp only [Pi.add_def, Pi.sub_def] at hd
  change fderiv ℝ (fun q : Coord => (b - q 1) ^ 8 * Real.exp (-lambda * q 1 + I q))
    p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;>
    simp [edgeDistance, directedWeight, weightPhase, coordPartial] <;> ring

theorem directedWeight_partial_t
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    coordPartial 0 (directedWeight b lambda I) p =
      directedWeight b lambda I p * coordPartial 0 I p := by
  simpa using directedWeight_partial b lambda hI 0

theorem directedWeight_partial_s
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) :
    coordPartial 1 (directedWeight b lambda I) p =
      -8 * (edgeDistance b p) ^ 7 * Real.exp (weightPhase lambda I p) +
        directedWeight b lambda I p * (coordPartial 1 I p - lambda) := by
  simpa using directedWeight_partial b lambda hI 1

theorem directedWeight_partial_edge_zero
    (b lambda : ℝ) (hI : DifferentiableAt ℝ I p) (hp : p 1 = b) (i : Fin 2) :
    coordPartial i (directedWeight b lambda I) p = 0 := by
  rw [directedWeight_partial b lambda hI i]
  simp [edgeDistance, directedWeight, hp]

theorem directedM_partial (b lambda : ℝ) (i : Fin 2) :
    coordPartial i (directedM b lambda I) p =
      -coordPartial i (directedWeight b lambda I) p := by
  change fderiv ℝ (fun q : Coord => -directedWeight b lambda I q) p (Pi.single i 1) =
    -fderiv ℝ (directedWeight b lambda I) p (Pi.single i 1)
  simp only [fderiv_fun_neg, neg_apply]

theorem directedN_partial
    (b lambda epsilon : ℝ) (hI : DifferentiableAt ℝ I p) (i : Fin 2) :
    coordPartial i (directedN b lambda epsilon I) p =
      epsilon * (if (0 : Fin 2) = i then 1 else 0) * directedWeight b lambda I p +
        epsilon * p 0 * coordPartial i (directedWeight b lambda I) p := by
  have hd := ((hasFDerivAt_apply (𝕜 := ℝ) 0 p).const_mul epsilon).fun_mul
    (directedWeight_differentiableAt b lambda hI).hasFDerivAt
  change fderiv ℝ (fun q : Coord => epsilon * q 0 * directedWeight b lambda I q)
    p (Pi.single i 1) = _
  rw [hd.fderiv]
  fin_cases i <;> simp [coordPartial]
  ring

end SmoothLocal.Weighted

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

theorem coordinateRectangle_isOpen (R a b : ℝ) : IsOpen (coordinateRectangle R a b) := by
  change IsOpen (((fun p : Coord => p 0) ⁻¹' Ioo (-R) R) ∩
    ((fun p : Coord => p 1) ⁻¹' Ioo a b))
  exact (isOpen_Ioo.preimage (continuous_apply 0)).inter
    (isOpen_Ioo.preimage (continuous_apply 1))

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MultiplierDivergence
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted

open SmoothLocal.Geometry

def multiplierOperator (A B C u : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 (coordPartial 0 u) p + A p * coordPartial 1 (coordPartial 1 u) p +
    B p * coordPartial 0 u p + C p * coordPartial 1 u p

def multiplierTest (m n u : Coord → ℝ) (p : Coord) : ℝ :=
  m p * coordPartial 1 u p + n p * coordPartial 0 u p

def multiplierFluxT (A m n u : Coord → ℝ) (p : Coord) : ℝ :=
  m p * coordPartial 0 u p * coordPartial 1 u p +
    (1 / 2 : ℝ) * (n p * (coordPartial 0 u p) ^ 2) -
    (1 / 2 : ℝ) * (A p * n p * (coordPartial 1 u p) ^ 2)

def multiplierFluxS (A m n u : Coord → ℝ) (p : Coord) : ℝ :=
  (1 / 2 : ℝ) * (A p * m p * (coordPartial 1 u p) ^ 2) +
    A p * n p * coordPartial 0 u p * coordPartial 1 u p -
    (1 / 2 : ℝ) * (m p * (coordPartial 0 u p) ^ 2)

variable {A B C m n u : Coord → ℝ} {p : Coord} {U : Set Coord}

theorem multiplierFluxT_partial_t
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hn : DifferentiableAt ℝ n p)
    (hut : DifferentiableAt ℝ (coordPartial 0 u) p)
    (hus : DifferentiableAt ℝ (coordPartial 1 u) p) :
    coordPartial 0 (multiplierFluxT A m n u) p =
      coordPartial 0 m p * coordPartial 0 u p * coordPartial 1 u p +
      m p * coordPartial 0 (coordPartial 0 u) p * coordPartial 1 u p +
      m p * coordPartial 0 u p * coordPartial 0 (coordPartial 1 u) p +
      (coordPartial 0 n p * (coordPartial 0 u p) ^ 2 +
        2 * n p * coordPartial 0 u p * coordPartial 0 (coordPartial 0 u) p) / 2 -
      ((coordPartial 0 A p * n p + A p * coordPartial 0 n p) * (coordPartial 1 u p) ^ 2 +
        2 * A p * n p * coordPartial 1 u p * coordPartial 0 (coordPartial 1 u) p) / 2 := by
  have hd := (((hm.hasFDerivAt.fun_mul hut.hasFDerivAt).fun_mul hus.hasFDerivAt).add
    ((hn.hasFDerivAt.fun_mul (hut.hasFDerivAt.fun_mul hut.hasFDerivAt)).const_mul
      (1 / 2 : ℝ))).sub
    (((hA.hasFDerivAt.fun_mul hn.hasFDerivAt).fun_mul
      (hus.hasFDerivAt.fun_mul hus.hasFDerivAt)).const_mul (1 / 2 : ℝ))
  simp only [Pi.add_def, Pi.sub_def, coordPartial] at hd
  unfold multiplierFluxT
  simp only [pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

theorem multiplierFluxS_partial_s
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hn : DifferentiableAt ℝ n p)
    (hut : DifferentiableAt ℝ (coordPartial 0 u) p)
    (hus : DifferentiableAt ℝ (coordPartial 1 u) p) :
    coordPartial 1 (multiplierFluxS A m n u) p =
      ((coordPartial 1 A p * m p + A p * coordPartial 1 m p) * (coordPartial 1 u p) ^ 2 +
        2 * A p * m p * coordPartial 1 u p * coordPartial 1 (coordPartial 1 u) p) / 2 +
      (coordPartial 1 A p * n p + A p * coordPartial 1 n p) *
        coordPartial 0 u p * coordPartial 1 u p +
      A p * n p * coordPartial 1 (coordPartial 0 u) p * coordPartial 1 u p +
      A p * n p * coordPartial 0 u p * coordPartial 1 (coordPartial 1 u) p -
      (coordPartial 1 m p * (coordPartial 0 u p) ^ 2 +
        2 * m p * coordPartial 0 u p * coordPartial 1 (coordPartial 0 u) p) / 2 := by
  have hd := ((((hA.hasFDerivAt.fun_mul hm.hasFDerivAt).fun_mul
    (hus.hasFDerivAt.fun_mul hus.hasFDerivAt)).const_mul (1 / 2 : ℝ)).add
    (((hA.hasFDerivAt.fun_mul hn.hasFDerivAt).fun_mul hut.hasFDerivAt).fun_mul
      hus.hasFDerivAt)).sub
    ((hm.hasFDerivAt.fun_mul (hut.hasFDerivAt.fun_mul hut.hasFDerivAt)).const_mul
      (1 / 2 : ℝ))
  simp only [Pi.add_def, Pi.sub_def, coordPartial] at hd
  unfold multiplierFluxS
  simp only [pow_two, coordPartial]
  rw [hd.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul]
  ring

theorem multiplier_divergence_identity
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hn : DifferentiableAt ℝ n p) (hu : ContDiffOn ℝ ∞ u U)
    (hU : IsOpen U) (hp : p ∈ U) :
    multiplierOperator A B C u p * multiplierTest m n u p =
      coordPartial 0 (multiplierFluxT A m n u) p +
      coordPartial 1 (multiplierFluxS A m n u) p +
      multiplierT B m n p * (coordPartial 0 u p) ^ 2 +
      multiplierS A C m n p * (coordPartial 1 u p) ^ 2 +
      multiplierJ A B C m n p * coordPartial 0 u p * coordPartial 1 u p := by
  have hdu (i : Fin 2) : DifferentiableAt ℝ (coordPartial i u) p :=
    (((partial_contDiffOn hu hU i) p hp).contDiffAt
      (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [multiplierFluxT_partial_t hA hm hn (hdu 0) (hdu 1),
    multiplierFluxS_partial_s hA hm hn (hdu 0) (hdu 1)]
  unfold multiplierOperator multiplierTest multiplierT multiplierS multiplierJ
  rw [HessianCalculus.coordPartial_mul_at hA hm 1,
    HessianCalculus.coordPartial_mul_at hA hn 0,
    HessianCalculus.coordPartial_mul_at hA hn 1,
    coordPartial_comm hu hU hp 0 1]
  ring

theorem directed_flux_factor
    (A u I : Coord → ℝ) (b lambda epsilon : ℝ) (p : Coord) :
    multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p =
      directedWeight b lambda I p *
        (-coordPartial 0 u p * coordPartial 1 u p +
          epsilon * p 0 * (coordPartial 0 u p) ^ 2 / 2 -
          epsilon * p 0 * A p * (coordPartial 1 u p) ^ 2 / 2) ∧
    multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p =
      directedWeight b lambda I p *
        (-A p * (coordPartial 1 u p) ^ 2 / 2 +
          epsilon * p 0 * A p * coordPartial 0 u p * coordPartial 1 u p +
          (coordPartial 0 u p) ^ 2 / 2) := by
  constructor <;> simp only [multiplierFluxT, multiplierFluxS, directedM, directedN] <;> ring

theorem directed_flux_edge_zero
    (A u I : Coord → ℝ) (b lambda epsilon : ℝ) (p : Coord) (hp : p 1 = b) :
    multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p = 0 ∧
    multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p = 0 := by
  obtain ⟨ht, hs⟩ := directed_flux_factor A u I b lambda epsilon p
  rw [directedWeight_edge_zero b lambda I p hp, zero_mul] at ht hs
  exact ⟨ht, hs⟩

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_MultiplierIntegral
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def zeroRectangleBoundary (tl tr sb st : ℝ) (f : Coord → ℝ) : Prop :=
  (∀ s ∈ Icc sb st, f (boxPoint tl s) = 0 ∧ f (boxPoint tr s) = 0) ∧
    (∀ t ∈ Icc tl tr, f (boxPoint t sb) = 0 ∧ f (boxPoint t st) = 0)

variable {tl tr sb st : ℝ} {f g : Coord → ℝ}

theorem rectangleIntegral_eq_area (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f =
      ∫ p in Ioc tl tr ×ˢ Ioc sb st, f (boxPoint p.1 p.2) := by
  rw [rectangleIntegral_swap ht hs hf]
  simp_rw [intervalIntegral.integral_of_le ht, intervalIntegral.integral_of_le hs]
  have hi : IntegrableOn (fun p : ℝ × ℝ => f (boxPoint p.1 p.2))
      (Ioc tl tr ×ˢ Ioc sb st) (volume.prod volume) := by
    simpa only [← Measure.volume_eq_prod] using rectangle_area_integrable hf
  simpa only [← Measure.volume_eq_prod] using
    (setIntegral_prod (fun p : ℝ × ℝ => f (boxPoint p.1 p.2)) hi).symm

theorem rectangleIntegral_congr (ht : tl ≤ tr) (hs : sb ≤ st)
    (heq : EqOn f g (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st f = rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  apply intervalIntegral.integral_congr
  intro s hs'
  apply intervalIntegral.integral_congr
  intro t ht'
  exact heq (boxPoint_mem
    (by simpa only [uIcc_of_le ht] using ht')
    (by simpa only [uIcc_of_le hs] using hs'))

theorem rectangleIntegral_add (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st))
    (hg : ContinuousOn g (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => f p + g p) =
      rectangleIntegral tl tr sb st f + rectangleIntegral tl tr sb st g := by
  have hfg : ContinuousOn (fun p => f p + g p) (closedRectangle tl tr sb st) := hf.add hg
  rw [rectangleIntegral_eq_area ht hs hfg,
    rectangleIntegral_eq_area ht hs hf, rectangleIntegral_eq_area ht hs hg]
  exact integral_add (rectangle_area_integrable hf) (rectangle_area_integrable hg)

variable {U : Set Coord}

theorem rectangleIntegral_partial_t_zero
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ s ∈ Icc sb st, f (boxPoint tl s) = 0 ∧ f (boxPoint tr s) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 0 f) = 0 := by
  have hinner (s : ℝ) (hs' : s ∈ Icc sb st) :
      (∫ t in tl..tr, coordPartial 0 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun t => coordPartial 0 f (boxPoint t s)) (uIcc tl tr) := by
      rw [uIcc_of_le ht]
      exact (partial_contDiffOn hf hU 0).continuousOn.comp
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

theorem rectangleIntegral_partial_s_zero
    (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hbox : closedRectangle tl tr sb st ⊆ U)
    (hedge : ∀ t ∈ Icc tl tr, f (boxPoint t sb) = 0 ∧ f (boxPoint t st) = 0) :
    rectangleIntegral tl tr sb st (coordPartial 1 f) = 0 := by
  rw [rectangleIntegral_swap ht hs ((partial_contDiffOn hf hU 1).continuousOn.mono hbox)]
  have hinner (t : ℝ) (ht' : t ∈ Icc tl tr) :
      (∫ s in sb..st, coordPartial 1 f (boxPoint t s)) = 0 := by
    have hcont : ContinuousOn (fun s => coordPartial 1 f (boxPoint t s)) (uIcc sb st) := by
      rw [uIcc_of_le hs]
      exact (partial_contDiffOn hf hU 1).continuousOn.comp
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

def multiplierQuadratic (A B C m n u : Coord → ℝ) (p : Coord) : ℝ :=
  multiplierT B m n p * (coordPartial 0 u p) ^ 2 +
    multiplierS A C m n p * (coordPartial 1 u p) ^ 2 +
    multiplierJ A B C m n p * coordPartial 0 u p * coordPartial 1 u p

theorem multiplierFluxes_contDiffOn
    {A m n u : Coord → ℝ} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierFluxT A m n u) U ∧
      ContDiffOn ℝ ∞ (multiplierFluxS A m n u) U := by
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  constructor
  · exact (((hm.mul ht).mul hs).add
      (contDiffOn_const.mul (hn.mul (ht.pow 2)))).sub
      (contDiffOn_const.mul ((hA.mul hn).mul (hs.pow 2)))
  · exact ((contDiffOn_const.mul ((hA.mul hm).mul (hs.pow 2))).add
      (((hA.mul hn).mul ht).mul hs)).sub
      (contDiffOn_const.mul (hm.mul (ht.pow 2)))

theorem multiplierQuadratic_contDiffOn
    {A B C m n u : Coord → ℝ} (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierQuadratic A B C m n u) U := by
  have hhalf {v : Coord → ℝ} (hv : ContDiffOn ℝ ∞ v U) :
      ContDiffOn ℝ ∞ (fun p => v p / 2) U :=
    hv.div contDiffOn_const (fun _ _ => two_ne_zero)
  have hmt := partial_contDiffOn hm hU 0
  have hms := partial_contDiffOn hm hU 1
  have hnt := partial_contDiffOn hn hU 0
  have hAms := partial_contDiffOn (hA.mul hm) hU 1
  have hAnt := partial_contDiffOn (hA.mul hn) hU 0
  have hAns := partial_contDiffOn (hA.mul hn) hU 1
  have hT : ContDiffOn ℝ ∞ (multiplierT B m n) U :=
    (hhalf (hms.sub hnt)).add (hB.mul hn)
  have hS : ContDiffOn ℝ ∞ (multiplierS A C m n) U :=
    ((hhalf hAms.neg).add (hhalf hAnt)).add (hC.mul hm)
  have hJ : ContDiffOn ℝ ∞ (multiplierJ A B C m n) U :=
    ((hmt.neg.add (hB.mul hm)).sub hAns).add (hC.mul hn)
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  exact ((hT.mul (ht.pow 2)).add (hS.mul (hs.pow 2))).add ((hJ.mul ht).mul hs)

theorem integrated_multiplier_identity
    {A B C m n u : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hm : ContDiffOn ℝ ∞ m U)
    (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    (hmb : zeroRectangleBoundary tl tr sb st m)
    (hnb : zeroRectangleBoundary tl tr sb st n) :
    rectangleIntegral tl tr sb st (fun p =>
      multiplierOperator A B C u p * multiplierTest m n u p) =
        rectangleIntegral tl tr sb st (multiplierQuadratic A B C m n u) := by
  have hflux := multiplierFluxes_contDiffOn hU hA hm hn hu
  have hQ := multiplierQuadratic_contDiffOn hU hA hB hC hm hn hu
  have hFt0 : rectangleIntegral tl tr sb st (coordPartial 0 (multiplierFluxT A m n u)) = 0 := by
    apply rectangleIntegral_partial_t_zero ht hs hU hflux.1 hbox
    intro s hs'
    constructor <;> simp [multiplierFluxT, (hmb.1 s hs').1, (hmb.1 s hs').2,
      (hnb.1 s hs').1, (hnb.1 s hs').2]
  have hFs0 : rectangleIntegral tl tr sb st (coordPartial 1 (multiplierFluxS A m n u)) = 0 := by
    apply rectangleIntegral_partial_s_zero ht hs hU hflux.2 hbox
    intro t ht'
    constructor <;> simp [multiplierFluxS, (hmb.2 t ht').1, (hmb.2 t ht').2,
      (hnb.2 t ht').1, (hnb.2 t ht').2]
  have hFt := (partial_contDiffOn hflux.1 hU 0).continuousOn.mono hbox
  have hFs := (partial_contDiffOn hflux.2 hU 1).continuousOn.mono hbox
  calc
    rectangleIntegral tl tr sb st (fun p =>
        multiplierOperator A B C u p * multiplierTest m n u p) =
      rectangleIntegral tl tr sb st (fun p =>
        coordPartial 0 (multiplierFluxT A m n u) p +
          coordPartial 1 (multiplierFluxS A m n u) p + multiplierQuadratic A B C m n u p) := by
      apply rectangleIntegral_congr ht hs
      intro p hp
      have hpU := hbox hp
      have hd := multiplier_divergence_identity (B := B) (C := C)
        ((hA.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        ((hm.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
        ((hn.contDiffAt (hU.mem_nhds hpU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hu hU hpU
      dsimp only
      rw [hd]
      unfold multiplierQuadratic
      ring
    _ = rectangleIntegral tl tr sb st (coordPartial 0 (multiplierFluxT A m n u)) +
        rectangleIntegral tl tr sb st (coordPartial 1 (multiplierFluxS A m n u)) +
        rectangleIntegral tl tr sb st (multiplierQuadratic A B C m n u) := by
      have hsum : ContinuousOn (fun p => coordPartial 0 (multiplierFluxT A m n u) p +
          coordPartial 1 (multiplierFluxS A m n u) p) (closedRectangle tl tr sb st) :=
        hFt.add hFs
      rw [rectangleIntegral_add ht hs hsum (hQ.continuousOn.mono hbox),
        rectangleIntegral_add ht hs hFt hFs]
    _ = rectangleIntegral tl tr sb st (multiplierQuadratic A B C m n u) := by
      rw [hFt0, hFs0]
      ring

theorem cutoff_test_factor
    (chi I u : Coord → ℝ) (edge lambda epsilon : ℝ) (p : Coord) :
    multiplierTest (cutoffM chi edge lambda I) (cutoffN chi edge lambda epsilon I) u p =
      chi p * directedWeight edge lambda I p *
        (-coordPartial 1 u p + epsilon * p 0 * coordPartial 0 u p) := by
  unfold multiplierTest cutoffM cutoffN directedM directedN
  ring

theorem integrated_cutoff_directed_identity
    {A B C chi I u : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st) (hU : IsOpen U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hchi : ContDiffOn ℝ ∞ chi U)
    (hI : ContDiffOn ℝ ∞ I U) (hu : ContDiffOn ℝ ∞ u U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    (hchiSides : ∀ s ∈ Icc sb st, chi (boxPoint tl s) = 0 ∧ chi (boxPoint tr s) = 0)
    (hchiBottom : ∀ t ∈ Icc tl tr, chi (boxPoint t sb) = 0)
    (lambda epsilon : ℝ) :
    rectangleIntegral tl tr sb st (fun p => multiplierOperator A B C u p *
      multiplierTest (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u p) =
        rectangleIntegral tl tr sb st
          (multiplierQuadratic A B C (cutoffM chi st lambda I) (cutoffN chi st lambda epsilon I) u) := by
  have hW := directedWeight_contDiffOn st lambda hI
  have hm : ContDiffOn ℝ ∞ (cutoffM chi st lambda I) U := hchi.mul hW.neg
  have htcoord : ContDiffOn ℝ ∞ (fun p : Coord => p 0) U := contDiffOn_apply ℝ ℝ 0 U
  have hn : ContDiffOn ℝ ∞ (cutoffN chi st lambda epsilon I) U :=
    hchi.mul ((contDiffOn_const.mul htcoord).mul hW)
  have hedge : zeroRectangleBoundary tl tr sb st (cutoffM chi st lambda I) ∧
      zeroRectangleBoundary tl tr sb st (cutoffN chi st lambda epsilon I) := by
    constructor
    · constructor
      · intro s hs'
        simp [cutoffM, (hchiSides s hs').1, (hchiSides s hs').2]
      · intro t ht'
        have hz := directed_mn_edge_zero st lambda epsilon I (boxPoint t st)
          (by simp [boxPoint])
        simp [cutoffM, hchiBottom t ht', hz.1]
    · constructor
      · intro s hs'
        simp [cutoffN, (hchiSides s hs').1, (hchiSides s hs').2]
      · intro t ht'
        have hz := directed_mn_edge_zero st lambda epsilon I (boxPoint t st)
          (by simp [boxPoint])
        simp [cutoffN, hchiBottom t ht', hz.2]
  exact integrated_multiplier_identity ht hs hU hA hB hC hm hn hu hbox hedge.1 hedge.2

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

def flowField (q : Coord → ℝ) (t y : ℝ) : ℝ := -q (coordinatePoint t y)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowCurvature
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def capChartRho (Y : ℝ → ℝ → ℝ) (p : Coord) : ℝ :=
  1 / coordPartial 1 (capFlowHeight Y) p

theorem capChartDomain_isOpen : IsOpen capChartDomain := coordinateRectangle_isOpen _ _ _

variable {Y : ℝ → ℝ → ℝ}

theorem boxPoint_coord_eta (p : Coord) : boxPoint (p 0) (p 1) = p := by
  ext i
  fin_cases i <;> simp [boxPoint]

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowTransport
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

def capPullback (Y : ℝ → ℝ → ℝ) (u : Coord → ℝ) : Coord → ℝ := fun p => u (capChart Y p)

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticCutoff
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem transitionDerivativeBound_pos : 0 < transitionDerivativeBound :=
  (Classical.choose_spec exists_smoothTransition_derivative_bound).1

theorem smoothTransition_deriv_abs_le (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ transitionDerivativeBound :=
  (Classical.choose_spec exists_smoothTransition_derivative_bound).2 x

theorem intervalCutoff_deriv_zero_left {a b x : ℝ} (hab : a < b) (hx : x ≤ a) :
    deriv (intervalCutoff a b) x = 0 := by
  rw [intervalCutoff_deriv, smoothTransition_deriv_zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hab).le), zero_div]

theorem intervalCutoff_deriv_zero_right {a b x : ℝ} (hab : a < b) (hx : b ≤ x) :
    deriv (intervalCutoff a b) x = 0 := by
  rw [intervalCutoff_deriv, smoothTransition_deriv_zero_of_one_le
    ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith)), zero_div]

theorem intervalCutoff_deriv_abs_le {a b : ℝ} (hab : a < b) (x : ℝ) :
    |deriv (intervalCutoff a b) x| ≤ transitionDerivativeBound / (b - a) := by
  rw [intervalCutoff_deriv, abs_div, abs_of_pos (sub_pos.mpr hab)]
  exact div_le_div_of_nonneg_right (smoothTransition_deriv_abs_le _) (sub_pos.mpr hab).le

theorem intervalCutoff_deriv_support {a b x : ℝ} (hab : a < b)
    (hx : deriv (intervalCutoff a b) x ≠ 0) : a < x ∧ x < b := by
  constructor
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_left hab (le_of_not_gt h))
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_right hab (le_of_not_gt h))

theorem ellipticPhi_deriv_abs_le {c : ℝ} (hc : 0 < c) (x : ℝ) :
    |deriv (ellipticPhi c) x| ≤ 2 * transitionDerivativeBound / c := by
  have hh := intervalCutoff_deriv_abs_le (a := c / 2) (b := c) (by linarith) x
  change |deriv (intervalCutoff (c / 2) c) x| ≤ _
  have he : transitionDerivativeBound / (c - c / 2) =
      2 * transitionDerivativeBound / c := by field_simp <;> ring
  rw [he] at hh
  exact hh

theorem ellipticPhi_deriv_support {c x : ℝ} (hc : 0 < c)
    (hx : deriv (ellipticPhi c) x ≠ 0) : c / 2 < x ∧ x < c := by
  constructor
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_left (by linarith) (le_of_not_gt h))
  · by_contra h
    exact hx (intervalCutoff_deriv_zero_right (by linarith) (le_of_not_gt h))

theorem threeEdgeCutoff_partial (l0 l1 r1 r0 a0 a1 : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p =
      if i = 0 then
        deriv (intervalCutoff l0 l1) (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
          intervalCutoff a0 a1 (p 1) -
        intervalCutoff l0 l1 (p 0) * deriv (intervalCutoff (-r0) (-r1)) (-p 0) *
          intervalCutoff a0 a1 (p 1)
      else intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
        deriv (intervalCutoff a0 a1) (p 1) := by
  have hL := (((intervalCutoff_contDiff l0 l1).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (p 0)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 0 p)
  have hR := (((intervalCutoff_contDiff (-r0) (-r1)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (-p 0)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 0 p).neg
  have hS := (((intervalCutoff_contDiff a0 a1).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (p 1)).hasDerivAt).comp_hasFDerivAt
    p (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  have hd := (hL.fun_mul hR).fun_mul hS
  simp only [Function.comp_def, Pi.neg_apply] at hd
  change fderiv ℝ (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p (Pi.single i 1) = _
  change fderiv ℝ (fun q => intervalCutoff l0 l1 (q 0) *
    intervalCutoff (-r0) (-r1) (-q 0) * intervalCutoff a0 a1 (q 1)) p _ = _
  rw [hd.fderiv]
  fin_cases i <;> simp
  ring

theorem threeEdgeCutoff_partial_bounds {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord) :
    |coordPartial 0 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p| ≤
        transitionDerivativeBound / (l1 - l0) + transitionDerivativeBound / (r0 - r1) ∧
      |coordPartial 1 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p| ≤
        transitionDerivativeBound / (a1 - a0) := by
  have hleft := intervalCutoff_range l0 l1 (p 0)
  have hright := intervalCutoff_range (-r0) (-r1) (-p 0)
  have hbottom := intervalCutoff_range a0 a1 (p 1)
  constructor
  · rw [threeEdgeCutoff_partial]
    simp only [↓reduceIte]
    refine (abs_sub _ _).trans ?_
    apply add_le_add
    · exact (abs_mul_two_cutoffs_le _ _ _ hright hbottom).trans
        (intervalCutoff_deriv_abs_le hL _)
    · rw [mul_comm (intervalCutoff l0 l1 (p 0))]
      exact (abs_mul_two_cutoffs_le _ _ _ hleft hbottom).trans
        (by simpa only [neg_sub_neg] using intervalCutoff_deriv_abs_le (neg_lt_neg hR) (-p 0))
  · rw [threeEdgeCutoff_partial]
    simp only [show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte]
    have he : intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) *
        deriv (intervalCutoff a0 a1) (p 1) = deriv (intervalCutoff a0 a1) (p 1) *
        intervalCutoff l0 l1 (p 0) * intervalCutoff (-r0) (-r1) (-p 0) := by ring
    rw [he]
    exact (abs_mul_two_cutoffs_le _ _ _ hleft hright).trans (intervalCutoff_deriv_abs_le hS _)

theorem threeEdgeCutoff_partial_t_support {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (p : Coord)
    (hp : coordPartial 0 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p ≠ 0) :
    p 0 ∈ Ioo l0 l1 ∨ p 0 ∈ Ioo r1 r0 := by
  by_cases hl : deriv (intervalCutoff l0 l1) (p 0) = 0
  · have hr : deriv (intervalCutoff (-r0) (-r1)) (-p 0) ≠ 0 := by
      intro h
      apply hp
      rw [threeEdgeCutoff_partial]
      simp [hl, h]
    have hs := intervalCutoff_deriv_support (neg_lt_neg hR) hr
    exact Or.inr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  · exact Or.inl (intervalCutoff_deriv_support hL hl)

theorem threeEdgeCutoff_partial_s_support {l0 l1 r1 r0 a0 a1 : ℝ}
    (hS : a0 < a1) (p : Coord)
    (hp : coordPartial 1 (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p ≠ 0) :
    p 1 ∈ Ioo a0 a1 := by
  apply intervalCutoff_deriv_support hS
  intro hz
  apply hp
  rw [threeEdgeCutoff_partial]
  simp [hz]

def capSpatialCutoff (L R A : ℝ) : Coord → ℝ :=
  threeEdgeCutoff (capOuterEdge L) (capInnerEdge L)
    (-capInnerEdge (-R)) (-capOuterEdge (-R)) (capOuterEdge A) (capInnerEdge A)

theorem capSpatialCutoff_contDiff (L R A : ℝ) :
    ContDiff ℝ ∞ (capSpatialCutoff L R A) := threeEdgeCutoff_contDiff _ _ _ _ _ _

theorem capSpatialCutoff_range (L R A : ℝ) (p : Coord) :
    0 ≤ capSpatialCutoff L R A p ∧ capSpatialCutoff L R A p ≤ 1 :=
  threeEdgeCutoff_range _ _ _ _ _ _ p

theorem capSpatialCutoff_one {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord)
    (hp : L ≤ p 0 ∧ p 0 ≤ R ∧ A ≤ p 1) : capSpatialCutoff L R A p = 1 := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  apply threeEdgeCutoff_one hli (neg_lt_neg hri) hai p
  exact ⟨by linarith [hp.1], by linarith [hp.2.1], by linarith [hp.2.2]⟩

theorem capSpatialCutoff_derivative_bands {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord) (i : Fin 2)
    (hp : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    (3 / 2 < |p 0| ∧ |p 0| < 2) ∨ (-2 < p 1 ∧ p 1 < -3 / 2) := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  fin_cases i
  · rcases threeEdgeCutoff_partial_t_support hli (neg_lt_neg hri) p hp with ht | ht
    · left
      rw [abs_of_neg (by linarith [ht.2] : p 0 < 0)]
      constructor <;> linarith [ht.1, ht.2]
    · left
      rw [abs_of_pos (by linarith [ht.1] : 0 < p 0)]
      constructor <;> linarith [ht.1, ht.2]
  · have hs := threeEdgeCutoff_partial_s_support hai p hp
    exact Or.inr ⟨by linarith [hs.1], by linarith [hs.2]⟩

theorem ellipticPhi_ratio_derivative_bound
    {c d k ki di M : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hM : 0 ≤ M) (hki : |ki| ≤ M) (hdi : |di| ≤ 1) :
    |deriv (ellipticPhi c) (k / d) * ((ki * d - k * di) / d ^ 2)| ≤
      (2 * transitionDerivativeBound / c) * (M + c) / d := by
  have hC : 0 ≤ 2 * transitionDerivativeBound / c :=
    div_nonneg (mul_nonneg (by norm_num) transitionDerivativeBound_pos.le) hc.le
  by_cases hzero : deriv (ellipticPhi c) (k / d) = 0
  · rw [hzero, zero_mul, abs_zero]
    exact div_nonneg (mul_nonneg hC (add_nonneg hM hc.le)) hd.le
  have hsupp := ellipticPhi_deriv_support hc hzero
  have hkpos : 0 < k := by
    have hpos : 0 < k / d := lt_trans (by linarith : 0 < c / 2) hsupp.1
    exact (div_pos_iff.mp hpos).elim (fun h => h.1) (fun h => False.elim (not_lt_of_ge hd.le h.2))
  have hkupper : |k| ≤ c * d := by
    rw [abs_of_pos hkpos]
    exact ((div_lt_iff₀ hd).mp hsupp.2).le
  have hnum : |ki * d - k * di| ≤ (M + c) * d := by
    calc
      |ki * d - k * di| ≤ |ki| * d + |k| * |di| := by
        simpa only [abs_mul, abs_of_pos hd] using abs_sub (ki * d) (k * di)
      _ ≤ M * d + (c * d) * 1 := add_le_add
        (mul_le_mul_of_nonneg_right hki hd.le)
        (mul_le_mul hkupper hdi (abs_nonneg di) (mul_nonneg hc.le hd.le))
      _ = (M + c) * d := by ring
  rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg d)]
  calc
    |deriv (ellipticPhi c) (k / d)| * (|ki * d - k * di| / d ^ 2) ≤
        (2 * transitionDerivativeBound / c) * (((M + c) * d) / d ^ 2) :=
      mul_le_mul (ellipticPhi_deriv_abs_le hc _) (div_le_div_of_nonneg_right hnum (sq_nonneg d))
        (div_nonneg (abs_nonneg _) (sq_nonneg d)) hC
    _ = (2 * transitionDerivativeBound / c) * (M + c) / d := by
      field_simp [hd.ne']

theorem edgeDistance_partial (b : ℝ) (p : Coord) (i : Fin 2) :
    coordPartial i (edgeDistance b) p = -(if (1 : Fin 2) = i then 1 else 0) := by
  have hd := (hasFDerivAt_const (𝕜 := ℝ) b p).sub (hasFDerivAt_apply (𝕜 := ℝ) 1 p)
  simp only [Pi.sub_def] at hd
  unfold coordPartial edgeDistance
  rw [hd.fderiv]
  fin_cases i <;> simp

theorem ellipticGate_partial {b c : ℝ} {K : Coord → ℝ} {p : Coord}
    (hK : DifferentiableAt ℝ K p) (hd : edgeDistance b p ≠ 0) (i : Fin 2) :
    coordPartial i (ellipticGate b c K) p =
      deriv (ellipticPhi c) (K p / edgeDistance b p) *
        ((coordPartial i K p * edgeDistance b p - K p * coordPartial i (edgeDistance b) p) /
          edgeDistance b p ^ 2) := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  have hquot : DifferentiableAt ℝ (fun q => K q / edgeDistance b q) p := by
    have hm : DifferentiableAt ℝ (fun q => K q * (edgeDistance b q)⁻¹) p :=
      hK.mul (hD.inv hd)
    simpa only [div_eq_mul_inv] using hm
  have hh := (((ellipticPhi_contDiff c).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    (K p / edgeDistance b p)).hasDerivAt).comp_hasFDerivAt p hquot.hasFDerivAt
  simp only [Function.comp_def] at hh
  have he : coordPartial i (ellipticGate b c K) p =
      deriv (ellipticPhi c) (K p / edgeDistance b p) *
        coordPartial i (fun q => K q / edgeDistance b q) p := by
    unfold coordPartial ellipticGate
    rw [hh.fderiv]
    simp only [smul_apply, smul_eq_mul]
  rw [he, coordPartial_div hK hD hd i]

theorem ellipticGate_partial_bound {b c M : ℝ} {K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hM : 0 ≤ M)
    (hK : DifferentiableAt ℝ K p) (i : Fin 2) (hKi : |coordPartial i K p| ≤ M) :
    |coordPartial i (ellipticGate b c K) p| ≤
      (2 * transitionDerivativeBound / c) * (M + c) / edgeDistance b p := by
  rw [ellipticGate_partial hK hd.ne' i]
  apply ellipticPhi_ratio_derivative_bound hc hd hM hKi
  rw [edgeDistance_partial]
  fin_cases i <;> (first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)

theorem ellipticAmplitude_partial {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hd : edgeDistance b p ≠ 0) (i : Fin 2) :
    coordPartial i (ellipticAmplitude b c chi K) p =
      3 * edgeDistance b p ^ 2 * coordPartial i (edgeDistance b) p * chi p * ellipticGate b c K p +
      edgeDistance b p ^ 3 * coordPartial i chi p * ellipticGate b c K p +
      edgeDistance b p ^ 3 * chi p * coordPartial i (ellipticGate b c K) p := by
  have hD : DifferentiableAt ℝ (edgeDistance b) p :=
    (differentiableAt_const b).sub (differentiableAt_apply (𝕜 := ℝ) 1 p)
  have hG := ellipticGate_differentiableAt (b := b) (c := c) hK hd
  have hdpow : coordPartial i (fun q => edgeDistance b q ^ 3) p =
      3 * edgeDistance b p ^ 2 * coordPartial i (edgeDistance b) p := by
    unfold coordPartial
    rw [(hD.hasFDerivAt.pow 3).fderiv]
    simp only [smul_apply, smul_eq_mul]
    ring
  unfold ellipticAmplitude
  rw [HessianCalculus.coordPartial_mul_at
      (f := fun q => edgeDistance b q ^ 3 * chi q) (h := ellipticGate b c K)
      ((hD.pow 3).mul hchi) hG i,
    HessianCalculus.coordPartial_mul_at (f := fun q => edgeDistance b q ^ 3) (h := chi)
      (hD.pow 3) hchi i, hdpow]
  ring

theorem ellipticWeight_partial {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hd : edgeDistance b p ≠ 0) (i : Fin 2) :
    coordPartial i (ellipticWeight b c chi K) p =
      2 * ellipticAmplitude b c chi K p * coordPartial i (ellipticAmplitude b c chi K) p := by
  have hA := ellipticAmplitude_differentiableAt (c := c) hchi hK hd
  have he : ellipticWeight b c chi K =
      fun q => ellipticAmplitude b c chi K q * ellipticAmplitude b c chi K q := by
    funext q
    rw [← ellipticAmplitude_sq, pow_two]
  rw [he, HessianCalculus.coordPartial_mul_at hA hA i]
  ring

theorem ellipticWeight_partial_bound {b c M X : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hd : 0 < edgeDistance b p) (hM : 0 ≤ M)
    (hchi : DifferentiableAt ℝ chi p) (hK : DifferentiableAt ℝ K p)
    (hchiRange : 0 ≤ chi p ∧ chi p ≤ 1) (i : Fin 2)
    (hchii : |coordPartial i chi p| ≤ X) (hKi : |coordPartial i K p| ≤ M) :
    |coordPartial i (ellipticWeight b c chi K) p| ≤
      2 * Real.sqrt (ellipticWeight b c chi K p) *
        (3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
          edgeDistance b p ^ 2 * ((2 * transitionDerivativeBound / c) * (M + c))) := by
  have hGRange : 0 ≤ ellipticGate b c K p ∧ ellipticGate b c K p ≤ 1 :=
    intervalCutoff_range _ _ _
  have hAi : |coordPartial i (ellipticAmplitude b c chi K) p| ≤
      3 * edgeDistance b p ^ 2 + edgeDistance b p ^ 3 * X +
        edgeDistance b p ^ 2 * ((2 * transitionDerivativeBound / c) * (M + c)) := by
    rw [ellipticAmplitude_partial hchi hK hd.ne' i]
    apply amplitude_derivative_algebra_bound hd hchiRange hGRange _ hchii
      (ellipticGate_partial_bound hc hd hM hK i hKi)
    rw [edgeDistance_partial]
    fin_cases i <;> (first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
  have hAmp : 0 ≤ ellipticAmplitude b c chi K p :=
    mul_nonneg (mul_nonneg (pow_pos hd _).le hchiRange.1) hGRange.1
  have hsqrt : Real.sqrt (ellipticWeight b c chi K p) = ellipticAmplitude b c chi K p := by
    rw [← ellipticAmplitude_sq, Real.sqrt_sq hAmp]
  rw [ellipticWeight_partial hchi hK hd.ne' i, abs_mul,
    abs_of_nonneg (mul_nonneg (by norm_num) hAmp), hsqrt]
  exact mul_le_mul_of_nonneg_left hAi (mul_nonneg (by norm_num) hAmp)

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapCutoffGeometry
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

def capOuterSpatialCutoff (L R A : ℝ) : Coord → ℝ :=
  capSpatialCutoff (capOuterEdge L) (-capOuterEdge (-R)) (capOuterEdge A)

theorem capOuterSpatialCutoff_contDiff (L R A : ℝ) :
    ContDiff ℝ ∞ (capOuterSpatialCutoff L R A) :=
  capSpatialCutoff_contDiff _ _ _

theorem capSpatialCutoff_nonzero_bounds {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) {p : Coord}
    (hp : capSpatialCutoff L R A p ≠ 0) :
    capOuterEdge L < p 0 ∧ p 0 < -capOuterEdge (-R) ∧ capOuterEdge A < p 1 := by
  obtain ⟨hlo, hli, hlu, hlx⟩ := capEdges_bounds hL
  obtain ⟨hro, hri, hru, hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao, hai, hau, hax⟩ := capEdges_bounds hA
  have hz (h : p 0 ≤ capOuterEdge L ∨ -capOuterEdge (-R) ≤ p 0 ∨
      p 1 ≤ capOuterEdge A) : capSpatialCutoff L R A p = 0 :=
    threeEdgeCutoff_zero hli (neg_lt_neg hri) hai p h
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    exact hp (hz (Or.inl (le_of_not_gt h)))
  · by_contra h
    exact hp (hz (Or.inr (Or.inl (le_of_not_gt h))))
  · by_contra h
    exact hp (hz (Or.inr (Or.inr (le_of_not_gt h))))

theorem capOuterSpatialCutoff_one_of_nonzero {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) {p : Coord}
    (hp : capSpatialCutoff L R A p ≠ 0) : capOuterSpatialCutoff L R A p = 1 := by
  have hlo := (capEdges_bounds hL).1
  have hro := (capEdges_bounds (x := -R) (by linarith)).1
  have hao := (capEdges_bounds hA).1
  obtain ⟨htl, htr, hsb⟩ := capSpatialCutoff_nonzero_bounds hL hR hA hp
  exact capSpatialCutoff_one hlo (by linarith) hao p ⟨htl.le, htr.le, hsb.le⟩

theorem capSpatialCutoff_nonzero_of_partial {L R A : ℝ} {p : Coord} {i : Fin 2}
    (hp : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    capSpatialCutoff L R A p ≠ 0 := by
  intro hz
  have hmin : IsLocalMin (capSpatialCutoff L R A) p := by
    change ∀ᶠ q in 𝓝 p, capSpatialCutoff L R A p ≤ capSpatialCutoff L R A q
    exact Filter.Eventually.of_forall (fun q => by
      simpa only [hz] using (capSpatialCutoff_range L R A q).1)
  have hd := hmin.fderiv_eq_zero
  exact hp (by simp [coordPartial, hd])

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem modelCurvature_lower_flow_bottom {kappa : ℝ} (hk : 0 < kappa)
    {Y : ℝ → ℝ → ℝ} {p : Coord}
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50) (hs : p 1 < -3 / 2) :
    kappa < modelCurvature kappa (capChart Y p) := by
  have hy : capFlowHeight Y p < -(37 / 25 : ℝ) := by
    linarith [(abs_le.mp hdisp).2]
  have hy2 : 2 < (capFlowHeight Y p)^2 := by
    nlinarith [sq_nonneg (capFlowHeight Y p + 37 / 25)]
  have hh := modelProfile_eq_one_sub_sq (y := capFlowHeight Y p) (by linarith)
  unfold modelCurvature
  rw [capChart_zero, capChart_one, hh]
  have hbase : 1 < (p 0)^2 - (1 - (capFlowHeight Y p)^2) := by
    nlinarith [sq_nonneg (p 0)]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hbase hk

theorem capChart_not_mem_patchBox_of_cutoff_band
    {Y : ℝ → ℝ → ℝ} {p : Coord}
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50)
    (hband : (3 / 2 < |p 0| ∧ |p 0| < 2) ∨ (-2 < p 1 ∧ p 1 < -3 / 2)) :
    capChart Y p ∉ patchBox := by
  intro hin
  rcases hband with ht | hs
  · have hxlo := hin.1 0
    have hxhi := hin.2 0
    simp only [capChart_zero] at hxlo hxhi
    have habs : |p 0| ≤ (1 : ℝ) / 10 := abs_le.mpr ⟨hxlo, hxhi⟩
    linarith [ht.1]
  · have hylo := hin.1 1
    simp only [capChart_one] at hylo
    linarith [hs.2, (abs_le.mp hdisp).2]

theorem capSpatialCutoff_partial_actual_curvature_lower
    {g0 eta : MetricField} {kappa L R A : ℝ} {U : Set Coord}
    {Y : ℝ → ℝ → ℝ} {p : Coord} {i : Fin 2}
    (hk : 0 < kappa) (hL : -2 < L) (hR : R < 2) (hA : -2 < A)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox) (hpU : capChart Y p ∈ U)
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50)
    (hpartial : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    kappa < capPullback Y (gaussianCurvature (g0 + eta)) p := by
  have hband := capSpatialCutoff_derivative_bands hL hR hA p i hpartial
  have hnot := capChart_not_mem_patchBox_of_cutoff_band hdisp hband
  have hts : capChart Y p ∉ tsupport eta := fun h => hnot (hsupport h)
  have hsame := gaussianCurvature_eq_of_eventuallyEq
    (metric_add_eventuallyEq_of_not_mem_tsupport g0 eta hts)
  change kappa < gaussianCurvature (g0 + eta) (capChart Y p)
  rw [hsame, hbackground _ hpU]
  rcases hband with ht | hs
  · have hh := modelCurvature_lateral_band_lower hk (p := capChart Y p)
      (by simpa only [capChart_zero] using ht.1)
    linarith
  · exact modelCurvature_lower_flow_bottom hk hdisp hs.2

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticEnergy
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

def ellipticErrorT (B v : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 v p - v p * B p

def ellipticErrorS (A C v : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 1 (fun q => A q * v q) p - v p * C p

def ellipticEnergy (A v u : Coord → ℝ) (p : Coord) : ℝ :=
  v p * ((coordPartial 0 u p) ^ 2 + A p * (coordPartial 1 u p) ^ 2)

def ellipticError (A B C v u : Coord → ℝ) (p : Coord) : ℝ :=
  u p * (ellipticErrorT B v p * coordPartial 0 u p +
    ellipticErrorS A C v p * coordPartial 1 u p)

def ellipticFluxT (v u : Coord → ℝ) (p : Coord) : ℝ :=
  -(v p * u p * coordPartial 0 u p)

def ellipticFluxS (A v u : Coord → ℝ) (p : Coord) : ℝ :=
  -(A p * v p * u p * coordPartial 1 u p)

variable {A B C v u f : Coord → ℝ} {U : Set Coord} {p : Coord}

theorem ellipticOperator_contDiffOn
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierOperator A B C u) U := by
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  exact (((partial_contDiffOn ht hU 0).add (hA.mul (partial_contDiffOn hs hU 1))).add
    (hB.mul ht)).add (hC.mul hs)

theorem rectangleIntegral_neg (tl tr sb st : ℝ) (g : Coord → ℝ) :
    rectangleIntegral tl tr sb st (fun p => -g p) = -rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  simp only [intervalIntegral.integral_neg]

theorem rectangleIntegral_const_mul (tl tr sb st c : ℝ) (g : Coord → ℝ) :
    rectangleIntegral tl tr sb st (fun p => c * g p) = c * rectangleIntegral tl tr sb st g := by
  unfold rectangleIntegral
  simp only [intervalIntegral.integral_const_mul]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticAbsorption
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem ellipticEnergy_nonneg (A v u : Coord → ℝ) (p : Coord)
    (hv : 0 ≤ v p) (hA : 0 < v p → 0 < A p) : 0 ≤ ellipticEnergy A v u p := by
  by_cases hz : v p = 0
  · simp [ellipticEnergy, hz]
  · have hvpos : 0 < v p := lt_of_le_of_ne hv (Ne.symm hz)
    exact mul_nonneg hv (add_nonneg (sq_nonneg _) (mul_nonneg (hA hvpos).le (sq_nonneg _)))

variable {tl tr sb st : ℝ}

theorem rectangleIntegral_sub {F G : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st (fun p => F p - G p) =
      rectangleIntegral tl tr sb st F - rectangleIntegral tl tr sb st G := by
  simp only [sub_eq_add_neg]
  have hneg : ContinuousOn (fun p => -G p) (closedRectangle tl tr sb st) := hG.neg
  rw [rectangleIntegral_add ht hs hF hneg, rectangleIntegral_neg]

theorem rectangleIntegral_mono {F G : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hG : ContinuousOn G (closedRectangle tl tr sb st))
    (hle : ∀ p ∈ closedRectangle tl tr sb st, F p ≤ G p) :
    rectangleIntegral tl tr sb st F ≤ rectangleIntegral tl tr sb st G := by
  rw [rectangleIntegral_eq_area ht hs hF, rectangleIntegral_eq_area ht hs hG]
  apply setIntegral_mono_on (rectangle_area_integrable hF) (rectangle_area_integrable hG)
    (measurableSet_Ioc.prod measurableSet_Ioc)
  intro p hp
  exact hle (boxPoint p.1 p.2) (boxPoint_mem
    (Ioc_subset_Icc_self hp.1) (Ioc_subset_Icc_self hp.2))

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticC1
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem coordPartial_continuousOn_one (hf : ContDiffOn ℝ 1 f U)
    (hU : IsOpen U) (i : Fin 2) : ContinuousOn (coordPartial i f) U := by
  have hd : ContDiffOn ℝ 0 (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by norm_num)
  exact (hd.clm_apply contDiffOn_const).continuousOn

variable {tl tr sb st : ℝ}

variable {A B C v u : Coord → ℝ}

theorem elliptic_fields_C1
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hC : ContDiffOn ℝ ∞ C U) (hv : ContDiffOn ℝ 1 v U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ 1 (ellipticFluxT v u) U ∧
    ContDiffOn ℝ 1 (ellipticFluxS A v u) U ∧
    ContinuousOn (ellipticEnergy A v u) U ∧
    ContinuousOn (ellipticError A B C v u) U := by
  have hA1 : ContDiffOn ℝ 1 A U := hA.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hu1 : ContDiffOn ℝ 1 u U := hu.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have ht := partial_contDiffOn hu hU 0
  have hs := partial_contDiffOn hu hU 1
  have ht1 : ContDiffOn ℝ 1 (coordPartial 0 u) U := ht.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hs1 : ContDiffOn ℝ 1 (coordPartial 1 u) U := hs.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hEt : ContinuousOn (ellipticErrorT B v) U :=
    (coordPartial_continuousOn_one hv hU 0).sub (hv.continuousOn.mul hB.continuousOn)
  have hEs : ContinuousOn (ellipticErrorS A C v) U :=
    (coordPartial_continuousOn_one (hA1.mul hv) hU 1).sub
      (hv.continuousOn.mul hC.continuousOn)
  exact ⟨((hv.mul hu1).mul ht1).neg, (((hA1.mul hv).mul hu1).mul hs1).neg,
    hv.continuousOn.mul ((ht.continuousOn.pow 2).add
      (hA.continuousOn.mul (hs.continuousOn.pow 2))),
    hu.continuousOn.mul ((hEt.mul ht.continuousOn).add (hEs.mul hs.continuousOn))⟩

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticCutoffEdge
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def ellipticEdgeDerivativeConstant (c : ℝ) : ℝ :=
  4 * (3 + (2 * transitionDerivativeBound / c) * (1 + c))

theorem ellipticEdgeRaw_partial_bound {c : ℝ} (hc : 0 < c) {p : Coord}
    (hp : p 1 < 0) (i : Fin 2) :
    |coordPartial i (ellipticEdgeRaw c) p| ≤
      (ellipticEdgeDerivativeConstant c / 2) * (-p 1) ^ 5 := by
  have hd : 0 < edgeDistance 0 p := by simpa only [edgeDistance, zero_sub] using neg_pos.mpr hp
  have hk : |coordPartial i (fun q : Coord => q 0) p| ≤ (1 : ℝ) := by
    unfold coordPartial
    rw [(hasFDerivAt_apply (𝕜 := ℝ) 0 p).fderiv]
    fin_cases i <;> (first | (simp [Pi.single_apply]; all_goals first | (norm_num [Pi.single_apply]; done) | rfl | decide) | (norm_num [Pi.single_apply]; done) | norm_num [Pi.single_apply])
  have hx : |coordPartial i (fun _ : Coord => (1 : ℝ)) p| ≤ (0 : ℝ) := by
    simp [coordPartial]
  have hh := ellipticWeight_partial_bound (b := 0) (c := c) (M := 1) (X := 0)
    hc hd (by norm_num) (differentiableAt_const 1)
    (differentiableAt_apply (𝕜 := ℝ) 0 p) ⟨by norm_num, le_rfl⟩ i hx hk
  have hsqrt : Real.sqrt (ellipticEdgeRaw c p) ≤ (edgeDistance 0 p) ^ 3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(pow_pos hd 3).le, ?_⟩
    dsimp only [ellipticEdgeRaw]
    convert ellipticWeight_le_distance_six 0 c (fun _ => 1) (fun p => p 0) p
      ⟨by norm_num, le_rfl⟩ using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hP : 0 ≤ (2 * transitionDerivativeBound / c) * (1 + c) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) transitionDerivativeBound_pos.le) hc.le)
      (by linarith)
  calc
    _ ≤ 2 * Real.sqrt (ellipticEdgeRaw c p) *
        (3 * edgeDistance 0 p ^ 2 + edgeDistance 0 p ^ 3 * 0 +
          edgeDistance 0 p ^ 2 * ((2 * transitionDerivativeBound / c) * (1 + c))) := hh
    _ ≤ 2 * edgeDistance 0 p ^ 3 *
        (3 * edgeDistance 0 p ^ 2 + edgeDistance 0 p ^ 3 * 0 +
          edgeDistance 0 p ^ 2 * ((2 * transitionDerivativeBound / c) * (1 + c))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
        (by positivity)
    _ = _ := by unfold ellipticEdgeDerivativeConstant edgeDistance; ring

theorem ellipticEdgeDerivative_norm_le {c : ℝ} (hc : 0 < c) (p : Coord) :
    ‖ellipticEdgeDerivative c p‖ ≤ ellipticEdgeDerivativeConstant c * |p 1| ^ 5 := by
  have hC : 0 ≤ ellipticEdgeDerivativeConstant c := by
    unfold ellipticEdgeDerivativeConstant
    have := transitionDerivativeBound_pos
    positivity
  unfold ellipticEdgeDerivative
  split_ifs with hp
  · calc
      _ ≤ |coordPartial 0 (ellipticEdgeRaw c) p| +
          |coordPartial 1 (ellipticEdgeRaw c) p| := coordLinear_norm_le _
      _ ≤ (ellipticEdgeDerivativeConstant c / 2) * (-p 1) ^ 5 +
          (ellipticEdgeDerivativeConstant c / 2) * (-p 1) ^ 5 :=
        add_le_add (ellipticEdgeRaw_partial_bound hc hp 0)
          (ellipticEdgeRaw_partial_bound hc hp 1)
      _ = _ := by rw [abs_of_neg hp]; ring
  · simp only [norm_zero]
    exact mul_nonneg hC (pow_nonneg (abs_nonneg _) _)

theorem ellipticEdgeDerivative_continuous {c : ℝ} (hc : 0 < c) :
    Continuous (ellipticEdgeDerivative c) := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases lt_trichotomy (p 1) 0 with hp | hp | hp
  · have hn := ellipticEdgeHalfPlane_isOpen.mem_nhds hp
    have hd := ((ellipticEdgeRaw_contDiffOn c).continuousOn_fderiv_of_isOpen
      ellipticEdgeHalfPlane_isOpen (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuousAt hn
    apply hd.congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    simp [ellipticEdgeDerivative, hq]
  · have hz : ellipticEdgeDerivative c p = 0 := by simp [ellipticEdgeDerivative, hp]
    change Tendsto (ellipticEdgeDerivative c) (𝓝 p) (𝓝 (ellipticEdgeDerivative c p))
    rw [hz, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (ellipticEdgeDerivative_norm_le hc)
    have hcont : Continuous (fun q : Coord => ellipticEdgeDerivativeConstant c * |q 1| ^ 5) :=
      continuous_const.mul (((continuous_apply 1).abs).pow 5)
    simpa [hp] using hcont.tendsto p
  · have hn : {q : Coord | 0 < q 1} ∈ 𝓝 p :=
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hp
    apply (continuousAt_const (y := (0 : Coord →L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    simp [ellipticEdgeDerivative, not_lt_of_ge hq.le]

theorem ellipticEdgeKernel_contDiff_one {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ 1 (ellipticEdgeKernel c) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨ellipticEdgeDerivative c, ellipticEdgeDerivative_continuous hc,
      ellipticEdgeKernel_hasFDerivAt c⟩

theorem ellipticWeightC1_partial_eq {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hp : p 1 < b) (i : Fin 2) :
    coordPartial i (ellipticWeightC1 b c chi K) p =
      coordPartial i (ellipticWeight b c chi K) p := by
  have he : ellipticWeightC1 b c chi K =ᶠ[𝓝 p] ellipticWeight b c chi K := by
    filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hp] with q hq
    exact ellipticWeightC1_eq hq.le
  unfold coordPartial
  rw [he.fderiv_eq]

theorem ellipticWeightC1_contDiffOn {b c : ℝ} {chi K : Coord → ℝ} {U : Set Coord}
    (hc : 0 < c) (hchi : ContDiffOn ℝ 1 chi U) (hK : ContDiffOn ℝ 1 K U) :
    ContDiffOn ℝ 1 (ellipticWeightC1 b c chi K) U := by
  have hmap : ContDiffOn ℝ 1 (fun p : Coord => ![K p, p 1 - b]) U := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · simpa using hK
    · simpa using (contDiffOn_apply ℝ ℝ 1 U).sub contDiffOn_const
  exact (hchi.pow 2).mul ((ellipticEdgeKernel_contDiff_one hc).comp_contDiffOn hmap)

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

theorem ellipticRatioConstant_nonneg {D c Cv M : ℝ}
    (hD : 0 ≤ D) (hc : 0 < c) (hM : 0 ≤ M) :
    0 ≤ ellipticRatioConstant D c Cv M := by
  unfold ellipticRatioConstant
  positivity

theorem ellipticCutoffDerivativeConstant_nonneg {c MK X : ℝ}
    (hc : 0 < c) (hMK : 0 ≤ MK) (hX : 0 ≤ X) :
    0 ≤ ellipticCutoffDerivativeConstant c MK X := by
  have htheta := transitionDerivativeBound_pos.le
  unfold ellipticCutoffDerivativeConstant
  positivity

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

theorem threeEdgeCutoff_partial_common {l0 l1 r1 r0 a0 a1 : ℝ}
    (hL : l0 < l1) (hR : r1 < r0) (hS : a0 < a1) (p : Coord) (i : Fin 2) :
    |coordPartial i (threeEdgeCutoff l0 l1 r1 r0 a0 a1) p| ≤
      threeEdgeDerivativeConstant l0 l1 r1 r0 a0 a1 := by
  have hb := threeEdgeCutoff_partial_bounds hL hR hS p
  have ht := transitionDerivativeBound_pos.le
  have hl : 0 ≤ transitionDerivativeBound / (l1 - l0) := div_nonneg ht (sub_pos.mpr hL).le
  have hr : 0 ≤ transitionDerivativeBound / (r0 - r1) := div_nonneg ht (sub_pos.mpr hR).le
  have hs : 0 ≤ transitionDerivativeBound / (a1 - a0) := div_nonneg ht (sub_pos.mpr hS).le
  unfold threeEdgeDerivativeConstant
  fin_cases i <;> simp only [Fin.mk_zero, Fin.mk_one] <;> linarith [hb.1, hb.2]

theorem ellipticWeightC1_errors_eq {b c : ℝ} (A B C chi K : Coord → ℝ)
    {p : Coord} (hp : p 1 < b) :
    ellipticErrorT B (ellipticWeightC1 b c chi K) p =
        ellipticErrorT B (ellipticWeight b c chi K) p ∧
      ellipticErrorS A C (ellipticWeightC1 b c chi K) p =
        ellipticErrorS A C (ellipticWeight b c chi K) p := by
  have he : (fun q => A q * ellipticWeightC1 b c chi K q) =ᶠ[𝓝 p]
      (fun q => A q * ellipticWeight b c chi K q) := by
    filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hp] with q hq
    rw [ellipticWeightC1_eq hq.le]
  have hderiv : coordPartial 1 (fun q => A q * ellipticWeightC1 b c chi K q) p =
      coordPartial 1 (fun q => A q * ellipticWeight b c chi K q) p := by
    unfold coordPartial
    rw [he.fderiv_eq]
  constructor
  · rw [ellipticErrorT, ellipticErrorT, ellipticWeightC1_partial_eq hp 0,
      ellipticWeightC1_eq hp.le]
  · rw [ellipticErrorS, ellipticErrorS, hderiv, ellipticWeightC1_eq hp.le]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_EllipticGradient
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

def weightedGradient (b : ℝ) (u : Coord → ℝ) (p : Coord) : ℝ :=
  edgeDistance b p ^ 7 * ((coordPartial 0 u p) ^ 2 + (coordPartial 1 u p) ^ 2)

theorem ellipticCutoff_gradient_pointwise
    {b c c1 g0 D : ℝ} {chi K G1 u : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hcc : c ≤ c1) (hg0 : 0 < g0)
    (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hchi : chi p = 1) (hK : c1 * edgeDistance b p ≤ K p) (hG1 : g0 ≤ G1 p) :
    weightedGradient b u p ≤ (D + 1 / (g0 * c1)) *
      ellipticEnergy (fun q => G1 q * K q) (ellipticWeight b c chi K) u p := by
  have hc1 : 0 < c1 := hc.trans_le hcc
  have hKpos : 0 < K p := (mul_pos hc1 hd).trans_le hK
  have hA : (g0 * c1) * edgeDistance b p ≤ G1 p * K p := by
    have h1 := mul_le_mul_of_nonneg_left hK hg0.le
    have h2 := mul_le_mul_of_nonneg_right hG1 hKpos.le
    nlinarith [h1, h2]
  unfold weightedGradient ellipticEnergy
  rw [ellipticWeight_eq_distance_six hc hcc hd hchi hK]
  exact elliptic_gradient_scalar hd hdD (mul_pos hg0 hc1) hA

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedCutoffBalance
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def multiplierCutoffError (A chi m n u : Coord → ℝ) (p : Coord) : ℝ :=
  coordPartial 0 chi p * multiplierFluxT A m n u p +
    coordPartial 1 chi p * multiplierFluxS A m n u p

theorem multiplier_divergence_quadratic
    {A B C m n u : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p) (hn : DifferentiableAt ℝ n p)
    (hu : ContDiffOn ℝ ∞ u U) (hU : IsOpen U) (hp : p ∈ U) :
    multiplierOperator A B C u p * multiplierTest m n u p =
      coordPartial 0 (multiplierFluxT A m n u) p + coordPartial 1 (multiplierFluxS A m n u) p +
        multiplierQuadratic A B C m n u p := by
  have hh := multiplier_divergence_identity (B := B) (C := C) hA hm hn hu hU hp
  unfold multiplierQuadratic
  linear_combination hh

theorem multiplierQuadratic_cutoff_split
    {A B C chi m n u : Coord → ℝ} {U : Set Coord} {p : Coord}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hchi : ContDiffOn ℝ ∞ chi U)
    (hm : ContDiffOn ℝ ∞ m U) (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U)
    (hp : p ∈ U) :
    multiplierQuadratic A B C (fun q => chi q * m q) (fun q => chi q * n q) u p =
      chi p * multiplierQuadratic A B C m n u p - multiplierCutoffError A chi m n u p := by
  have hAd := (hA.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hmd := (hm.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hnd := (hn.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hcd := (hchi.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hbase := multiplier_divergence_quadratic (B := B) (C := C) hAd hmd hnd hu hU hp
  have hcut := multiplier_divergence_quadratic (B := B) (C := C) hAd (hcd.mul hmd) (hcd.mul hnd) hu hU hp
  change multiplierOperator A B C u p *
      multiplierTest (fun q => chi q * m q) (fun q => chi q * n q) u p =
    coordPartial 0 (multiplierFluxT A (fun q => chi q * m q) (fun q => chi q * n q) u) p +
      coordPartial 1 (multiplierFluxS A (fun q => chi q * m q) (fun q => chi q * n q) u) p +
      multiplierQuadratic A B C (fun q => chi q * m q) (fun q => chi q * n q) u p at hcut
  have htest : multiplierTest (fun q => chi q * m q) (fun q => chi q * n q) u p =
      chi p * multiplierTest m n u p := by unfold multiplierTest; ring
  have hFt : multiplierFluxT A (fun q => chi q * m q) (fun q => chi q * n q) u =
      (fun q => chi q * multiplierFluxT A m n u q) := by funext q; unfold multiplierFluxT; ring
  have hFs : multiplierFluxS A (fun q => chi q * m q) (fun q => chi q * n q) u =
      (fun q => chi q * multiplierFluxS A m n u q) := by funext q; unfold multiplierFluxS; ring
  obtain ⟨hFts, hFss⟩ := multiplierFluxes_contDiffOn hU hA hm hn hu
  rw [htest, hFt, hFs,
    HessianCalculus.coordPartial_mul_at (f := chi) (h := multiplierFluxT A m n u) hcd
      ((hFts.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) 0,
    HessianCalculus.coordPartial_mul_at (f := chi) (h := multiplierFluxS A m n u) hcd
      ((hFss.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) 1] at hcut
  unfold multiplierCutoffError
  linear_combination chi p * hbase - hcut

theorem multiplierCutoffError_contDiffOn
    {A chi m n u : Coord → ℝ} {U : Set Coord}
    (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U) (hchi : ContDiffOn ℝ ∞ chi U)
    (hm : ContDiffOn ℝ ∞ m U) (hn : ContDiffOn ℝ ∞ n U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (multiplierCutoffError A chi m n u) U := by
  obtain ⟨hFt, hFs⟩ := multiplierFluxes_contDiffOn hU hA hm hn hu
  exact ((partial_contDiffOn hchi hU 0).mul hFt).add ((partial_contDiffOn hchi hU 1).mul hFs)

theorem multiplierCutoffError_zero (A chi m n u : Coord → ℝ) (p : Coord)
    (ht : coordPartial 0 chi p = 0) (hs : coordPartial 1 chi p = 0) :
    multiplierCutoffError A chi m n u p = 0 := by simp [multiplierCutoffError, ht, hs]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedIntegralEstimate
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

def directedGradientEnergy (chi I u : Coord → ℝ) (edge lambda : ℝ) (p : Coord) : ℝ :=
  chi p * directedWeight edge lambda I p * ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2)

def directedCutoffError (A chi I u : Coord → ℝ) (edge lambda epsilon : ℝ) : Coord → ℝ :=
  multiplierCutoffError A chi (directedM edge lambda I) (directedN edge lambda epsilon I) u

def directedCoercivityDefect (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord) : ℝ :=
  chi p * max 0 (c * directedWeight edge lambda I p *
    ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) -
      multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p)

theorem directedCoercivityDefect_zero
    (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord)
    (hcoercive : c * directedWeight edge lambda I p *
      ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) ≤
        multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p) :
    directedCoercivityDefect A B C chi I u edge lambda epsilon c p = 0 := by
  simp only [directedCoercivityDefect, max_eq_left (sub_nonpos.mpr hcoercive), mul_zero]

theorem directedCoercivityDefect_domination
    (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord) (hchi : 0 ≤ chi p) :
    c * directedGradientEnergy chi I u edge lambda p ≤
      chi p * multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p +
        directedCoercivityDefect A B C chi I u edge lambda epsilon c p := by
  have hh := mul_le_mul_of_nonneg_left
    (le_max_right (0 : ℝ) (c * directedWeight edge lambda I p *
      ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) -
        multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p)) hchi
  dsimp [directedGradientEnergy, directedCoercivityDefect]
  nlinarith only [hh]

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedEdgeDefect
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem directedQuadratic_edge_zero
    (A B C I u : Coord → ℝ) (edge lambda epsilon : ℝ) (p : Coord)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p) (hedge : p 1 = edge) :
    multiplierQuadratic A B C (directedM edge lambda I) (directedN edge lambda epsilon I) u p = 0 := by
  have hW := directedWeight_edge_zero edge lambda I p hedge
  have hWd (i : Fin 2) := directedWeight_partial_edge_zero edge lambda hI hedge i
  have hm := directedM_differentiableAt edge lambda hI
  have hn := directedN_differentiableAt edge lambda epsilon hI
  obtain ⟨hm0, hn0⟩ := directed_mn_edge_zero edge lambda epsilon I p hedge
  have hmd (i : Fin 2) : coordPartial i (directedM edge lambda I) p = 0 := by
    rw [directedM_partial, hWd i, neg_zero]
  have hnd (i : Fin 2) : coordPartial i (directedN edge lambda epsilon I) p = 0 := by
    rw [directedN_partial edge lambda epsilon hI i, hW, hWd i]
    ring
  have hAm (i : Fin 2) : coordPartial i (fun q => A q * directedM edge lambda I q) p = 0 := by
    rw [HessianCalculus.coordPartial_mul_at hA hm i, hm0, hmd i]
    ring
  have hAn (i : Fin 2) : coordPartial i (fun q => A q * directedN edge lambda epsilon I q) p = 0 := by
    rw [HessianCalculus.coordPartial_mul_at hA hn i, hn0, hnd i]
    ring
  simp only [multiplierQuadratic, multiplierT, multiplierS, multiplierJ,
    hmd, hnd, hAm, hAn, hm0, hn0]
  ring

theorem directedCutoffError_edge_zero
    (A chi I u : Coord → ℝ) (edge lambda epsilon : ℝ) (p : Coord) (hedge : p 1 = edge) :
    directedCutoffError A chi I u edge lambda epsilon p = 0 := by
  obtain ⟨ht, hs⟩ := directed_flux_edge_zero A u I edge lambda epsilon p hedge
  simp [directedCutoffError, multiplierCutoffError, ht, hs]

theorem directedCoercivityDefect_edge_zero
    (A B C chi I u : Coord → ℝ) (edge lambda epsilon c : ℝ) (p : Coord)
    (hA : DifferentiableAt ℝ A p) (hI : DifferentiableAt ℝ I p) (hedge : p 1 = edge) :
    directedCoercivityDefect A B C chi I u edge lambda epsilon c p = 0 := by
  rw [directedCoercivityDefect, directedWeight_edge_zero edge lambda I p hedge,
    directedQuadratic_edge_zero A B C I u edge lambda epsilon p hA hI hedge]
  simp

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

theorem capOverlapThreshold_pos {kappa c1 D : ℝ}
    (hk : 0 < kappa) (hc1 : 0 < c1) (hD : 0 ≤ D) :
    0 < capOverlapThreshold kappa c1 D := by
  exact lt_min hc1 (div_pos hk (by linarith))

theorem capOverlapThreshold_le (kappa c1 D : ℝ) :
    capOverlapThreshold kappa c1 D ≤ c1 := min_le_left _ _

theorem capOverlapThreshold_distance_le {kappa c1 D d : ℝ}
    (hk : 0 < kappa) (hc1 : 0 < c1) (hD : 0 ≤ D) (_ : 0 ≤ d) (hdD : d ≤ D) :
    capOverlapThreshold kappa c1 D * d ≤ kappa := by
  have hc := (capOverlapThreshold_pos hk hc1 hD).le
  have hD1 : 0 < D + 1 := by linarith
  have hcd : capOverlapThreshold kappa c1 D * (D + 1) ≤ kappa :=
    (le_div_iff₀ hD1).mp (min_le_right _ _)
  exact (mul_le_mul_of_nonneg_left (show d ≤ D + 1 by linarith) hc).trans hcd

theorem capOuterElliptic_gradient_pointwise
    {L R A b c g0 D : ℝ} {K G1 u : Coord → ℝ} {p : Coord}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A)
    (hc : 0 < c) (hg0 : 0 < g0) (hd : 0 < edgeDistance b p)
    (hdD : edgeDistance b p ≤ D) (hchi : capSpatialCutoff L R A p ≠ 0)
    (hK : c * edgeDistance b p ≤ K p) (hG1 : g0 ≤ G1 p) :
    weightedGradient b u p ≤ (D + 1 / (g0 * c)) *
      ellipticEnergy (fun q => G1 q * K q)
        (ellipticWeightC1 b c (capOuterSpatialCutoff L R A) K) u p := by
  have houter := capOuterSpatialCutoff_one_of_nonzero hL hR hA hchi
  have hh := ellipticCutoff_gradient_pointwise (u := u) hc le_rfl hg0 hd hdD houter hK hG1
  have hp : p 1 ≤ b := (sub_pos.mp hd).le
  simpa only [ellipticEnergy, ellipticWeightC1_eq hp] using hh

theorem directedCoercivityDefect_nonzero_cutoff
    {A B C chi I u : Coord → ℝ} {b lambda epsilon c2 : ℝ} {p : Coord}
    (hdef : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≠ 0) : chi p ≠ 0 := by
  intro hz
  apply hdef
  simp only [directedCoercivityDefect, hz, zero_mul]

theorem capOuterElliptic_gradient_on_defect
    {L R A0 b c1 c2 kappa D g0 lambda epsilon : ℝ}
    {A B C K G1 I u : Coord → ℝ} {p : Coord}
    (hL : -2 < L) (hR : R < 2) (hA0 : -2 < A0)
    (hk : 0 < kappa) (hc1 : 0 < c1) (hD : 0 ≤ D) (hg0 : 0 < g0)
    (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D) (hG1 : g0 ≤ G1 p)
    (hcoercive : K p ≤ c1 * edgeDistance b p →
      c2 * directedWeight b lambda I p * ((coordPartial 0 u p)^2 + (coordPartial 1 u p)^2) ≤
        multiplierQuadratic A B C (directedM b lambda I) (directedN b lambda epsilon I) u p)
    (hdef : directedCoercivityDefect A B C (capSpatialCutoff L R A0) I u b lambda epsilon c2 p ≠ 0) :
    weightedGradient b u p ≤ (D + 1 / (g0 * capOverlapThreshold kappa c1 D)) *
      ellipticEnergy (fun q => G1 q * K q)
        (ellipticWeightC1 b (capOverlapThreshold kappa c1 D) (capOuterSpatialCutoff L R A0) K) u p := by
  have hK : c1 * edgeDistance b p < K p := by
    by_contra h
    exact hdef (directedCoercivityDefect_zero _ _ _ _ _ _ _ _ _ _ _ (hcoercive (le_of_not_gt h)))
  apply capOuterElliptic_gradient_pointwise hL hR hA0 (capOverlapThreshold_pos hk hc1 hD)
    hg0 hd hdD (directedCoercivityDefect_nonzero_cutoff hdef) _ hG1
  exact (mul_le_mul_of_nonneg_right (capOverlapThreshold_le kappa c1 D) hd.le).trans hK.le

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted

theorem capOuterElliptic_gradient_on_actual_cutoff_support
    {g0 eta : MetricField} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    {L R A b kappa c1 D glow : ℝ} {G1 u : Coord → ℝ} {p : Coord} {i : Fin 2}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (hk : 0 < kappa)
    (hc1 : 0 < c1) (hD : 0 ≤ D) (hg : 0 < glow)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = SmoothLocal.Model.modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox) (hpU : capChart Y p ∈ U)
    (hdisp : |capFlowHeight Y p - p 1| ≤ (1 : ℝ) / 50)
    (hd : 0 < edgeDistance b p) (hdD : edgeDistance b p ≤ D) (hG1 : glow ≤ G1 p)
    (hpartial : coordPartial i (capSpatialCutoff L R A) p ≠ 0) :
    weightedGradient b u p ≤ (D + 1 / (glow * capOverlapThreshold kappa c1 D)) *
      ellipticEnergy (fun q => G1 q * capPullback Y (gaussianCurvature (g0 + eta)) q)
        (ellipticWeightC1 b (capOverlapThreshold kappa c1 D) (capOuterSpatialCutoff L R A)
          (capPullback Y (gaussianCurvature (g0 + eta)))) u p := by
  have hK := capSpatialCutoff_partial_actual_curvature_lower hk hL hR hA hbackground hsupport
    hpU hdisp hpartial
  apply capOuterElliptic_gradient_pointwise hL hR hA (capOverlapThreshold_pos hk hc1 hD)
    hg hd hdD (capSpatialCutoff_nonzero_of_partial hpartial) _ hG1
  exact (capOverlapThreshold_distance_le hk hc1 hD hd.le hdD).trans hK.le

end SmoothLocal.Flow

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

theorem directedCutoffError_abs_le_seven
    {A chi I u : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M X : ℝ}
    (hlambda : 0 ≤ lambda) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (ht : |p 0| ≤ 2) (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hI : |I p| ≤ MI) (hA : |A p| ≤ M)
    (hchi : ∀ i : Fin 2, |coordPartial i chi p| ≤ X) :
    |directedCutoffError A chi I u b lambda epsilon p| ≤
      (6*X*D*Real.exp (lambda*S+MI)*(M+1)) * weightedGradient b u p := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hA
  have hX : 0 ≤ X := (abs_nonneg _).trans (hchi 0)
  have hD : 0 ≤ D := hd.trans hdD
  have hW : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have he : |epsilon*p 0| ≤ (2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg heps]
    exact (mul_le_mul_of_nonneg_left ht heps).trans (by linarith)
  obtain ⟨hT, hS⟩ := directedFlux_scalar_bound (x := coordPartial 0 u p)
    (y := coordPartial 1 u p) he hA
  obtain ⟨hFt, hFs⟩ := directed_flux_factor A u I b lambda epsilon p
  have hT' : |multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p| ≤
      directedWeight b lambda I p * (3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2)) := by
    rw [hFt, abs_mul, abs_of_nonneg hW]
    exact mul_le_mul_of_nonneg_left hT hW
  have hS' : |multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p| ≤
      directedWeight b lambda I p * (3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2)) := by
    rw [hFs, abs_mul, abs_of_nonneg hW]
    exact mul_le_mul_of_nonneg_left hS hW
  have hbound : 0 ≤ directedWeight b lambda I p *
      (3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2)) := by positivity
  have hbase : |directedCutoffError A chi I u b lambda epsilon p| ≤
      6*X*(M+1)*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) := by
    unfold directedCutoffError multiplierCutoffError
    calc
      _ ≤ |coordPartial 0 chi p * multiplierFluxT A (directedM b lambda I) (directedN b lambda epsilon I) u p| +
          |coordPartial 1 chi p * multiplierFluxS A (directedM b lambda I) (directedN b lambda epsilon I) u p| :=
        abs_add_le _ _
      _ ≤ X*(directedWeight b lambda I p*(3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2))) +
          X*(directedWeight b lambda I p*(3*(M+1)*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2))) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul (hchi 0) hT' (abs_nonneg _) hX)
          (mul_le_mul (hchi 1) hS' (abs_nonneg _) hX)
      _ = _ := by ring
  have hWbound := directedWeight_le_seven hlambda hd hdD hs hI
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWbound
    (show 0 ≤ 6*X*(M+1) by positivity))
      (add_nonneg (sq_nonneg (coordPartial 0 u p)) (sq_nonneg (coordPartial 1 u p)))
  exact hbase.trans (by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    unfold weightedGradient
    ring)

theorem capSpatialCutoff_partial_uniform {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (p : Coord) (i : Fin 2) :
    |coordPartial i (capSpatialCutoff L R A) p| ≤ capSpatialDerivativeConstant L R A := by
  exact threeEdgeCutoff_partial_common (capEdges_bounds hL).2.1
    (neg_lt_neg (capEdges_bounds (x := -R) (by linarith)).2.1) (capEdges_bounds hA).2.1 p i

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedWeightJetCost
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem directedWeightJetBudget_bounds {D M lambda : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hlambda : 0 ≤ lambda) :
    0 ≤ directedWeightJetBudget D M lambda ∧
    D ≤ directedWeightJetBudget D M lambda ∧
    2*D ≤ directedWeightJetBudget D M lambda ∧
    D*M ≤ directedWeightJetBudget D M lambda ∧
    8+D*(M+lambda) ≤ directedWeightJetBudget D M lambda ∧
    D+2*D*M ≤ directedWeightJetBudget D M lambda ∧
    16+2*D*(M+lambda) ≤ directedWeightJetBudget D M lambda := by
  have hDM := mul_nonneg hD hM
  have hDl := mul_nonneg hD hlambda
  unfold directedWeightJetBudget
  constructor
  · positivity
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem directedWeight_value_and_partials_bound
    {I : Coord → ℝ} {p : Coord} {b lambda D S MI M : ℝ}
    (hId : DifferentiableAt ℝ I p) (hlambda : 0 ≤ lambda) (hM : 0 ≤ M)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M) :
    |directedWeight b lambda I p| ≤ D*(Real.exp (lambda*S+MI)*edgeDistance b p^7) ∧
    |coordPartial 0 (directedWeight b lambda I) p| ≤
      (D*M)*(Real.exp (lambda*S+MI)*edgeDistance b p^7) ∧
    |coordPartial 1 (directedWeight b lambda I) p| ≤
      (8+D*(M+lambda))*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
  have hD : 0 ≤ D := hd.trans hdD
  have hW : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have hE : 0 ≤ Real.exp (lambda*S+MI)*edgeDistance b p^7 := by positivity
  have hw : |directedWeight b lambda I p| ≤ D*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
    rw [abs_of_nonneg hW]
    convert directedWeight_le_seven hlambda hd hdD hs hIv using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hphase : weightPhase lambda I p ≤ lambda*S+MI := by
    have hs' : -p 1 ≤ S := by linarith [(abs_le.mp hs).1]
    have hm := mul_le_mul_of_nonneg_left hs' hlambda
    unfold weightPhase
    linarith [(abs_le.mp hIv).2]
  refine ⟨hw, ?_, ?_⟩
  · rw [directedWeight_partial_t b lambda hId, abs_mul]
    have hh := mul_le_mul hw (hIi 0) (abs_nonneg _) (mul_nonneg hD hE)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · rw [directedWeight_partial_s b lambda hId]
    have hIs : |coordPartial 1 I p - lambda| ≤ M+lambda := by
      calc
        _ ≤ |coordPartial 1 I p| + |lambda| := abs_sub _ _
        _ ≤ M+lambda := by rw [abs_of_nonneg hlambda]; exact add_le_add (hIi 1) le_rfl
    have hlead : |-8*edgeDistance b p^7*Real.exp (weightPhase lambda I p)| ≤
        8*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
      have hh := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase)
        (show 0 ≤ 8*edgeDistance b p^7 by positivity)
      calc
        _ = 8*edgeDistance b p^7*Real.exp (weightPhase lambda I p) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hd 7),
            abs_of_pos (Real.exp_pos _)]
          norm_num
        _ ≤ 8*edgeDistance b p^7*Real.exp (lambda*S+MI) := hh
        _ = _ := by ring
    have hrest : |directedWeight b lambda I p*(coordPartial 1 I p-lambda)| ≤
        (D*(M+lambda))*(Real.exp (lambda*S+MI)*edgeDistance b p^7) := by
      rw [abs_mul]
      calc
        _ ≤ (D*(Real.exp (lambda*S+MI)*edgeDistance b p^7))*(M+lambda) :=
          (mul_le_mul_of_nonneg_left hIs (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_right hw (add_nonneg hM hlambda))
        _ = _ := by ring
    exact (abs_add_le _ _).trans (by
      have hh := add_le_add hlead hrest
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring)

theorem directedMultiplier_firstJet_abs_le_seven
    {I : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M : ℝ}
    (hId : DifferentiableAt ℝ I p) (hlambda : 0 ≤ lambda) (hM : 0 ≤ M)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ 2)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M) :
    let V := directedWeightJetBudget D M lambda * Real.exp (lambda*S+MI)*edgeDistance b p^7
    |directedM b lambda I p| ≤ V ∧ |directedN b lambda epsilon I p| ≤ V ∧
      (∀ i : Fin 2, |coordPartial i (directedM b lambda I) p| ≤ V) ∧
      (∀ i : Fin 2, |coordPartial i (directedN b lambda epsilon I) p| ≤ V) := by
  let E := Real.exp (lambda*S+MI)*edgeDistance b p^7
  have hE : 0 ≤ E := by dsimp [E] <;> positivity
  have hD : 0 ≤ D := hd.trans hdD
  have het : |epsilon*p 0| ≤ (2 : ℝ) := by
    rw [abs_mul, abs_of_nonneg heps]
    exact (mul_le_mul_of_nonneg_left ht heps).trans (by linarith)
  have heabs : |epsilon| ≤ 1 := by rwa [abs_of_nonneg heps]
  obtain ⟨hw, hwt, hws⟩ := directedWeight_value_and_partials_bound hId hlambda hM hd hdD hs hIv hIi
  obtain ⟨hN, hND, hN2D, hNDM, hNs, hNt, hNss⟩ := directedWeightJetBudget_bounds hD hM hlambda
  change |directedWeight b lambda I p| ≤ D*E at hw
  change |coordPartial 0 (directedWeight b lambda I) p| ≤ (D*M)*E at hwt
  change |coordPartial 1 (directedWeight b lambda I) p| ≤ (8+D*(M+lambda))*E at hws
  have hlift {a x : ℝ} (hx : |x| ≤ a*E) (ha : a ≤ directedWeightJetBudget D M lambda) :
      |x| ≤ directedWeightJetBudget D M lambda*Real.exp (lambda*S+MI)*edgeDistance b p^7 := by
    have hh := hx.trans (mul_le_mul_of_nonneg_right ha hE)
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [E]
    ring
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold directedM
    rw [abs_neg]
    exact hlift hw hND
  · have hh : |directedN b lambda epsilon I p| ≤ (2*D)*E := by
      unfold directedN
      rw [abs_mul]
      convert mul_le_mul het hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) using 1
      all_goals try with_reducible_and_instances rfl
      ring
    exact hlift hh hN2D
  · intro i
    rw [directedM_partial b lambda i, abs_neg]
    fin_cases i
    · simpa only [Fin.mk_zero] using hlift hwt hNDM
    · simpa only [Fin.mk_one] using hlift hws hNs
  · intro i
    rw [directedN_partial b lambda epsilon hId i]
    fin_cases i
    · simp only [Fin.mk_zero, Fin.isValue, ↓reduceIte, mul_one]
      have hfirst : |epsilon*directedWeight b lambda I p| ≤ D*E := by
        rw [abs_mul]
        have hh := mul_le_mul heabs hw (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        simpa only [one_mul] using hh
      have hsecond : |epsilon*p 0*coordPartial 0 (directedWeight b lambda I) p| ≤ (2*D*M)*E := by
        rw [abs_mul]
        convert mul_le_mul het hwt (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) using 1
        all_goals try with_reducible_and_instances rfl
        ring
      have hh : |epsilon*directedWeight b lambda I p +
          epsilon*p 0*coordPartial 0 (directedWeight b lambda I) p| ≤ (D+2*D*M)*E := by
        exact (abs_add_le _ _).trans (by
          convert add_le_add hfirst hsecond using 1
          all_goals try with_reducible_and_instances rfl
          ring)
      exact hlift hh hNt
    · simp only [Fin.mk_one, Fin.isValue, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte,
        mul_zero, zero_mul, zero_add]
      have hh : |epsilon*p 0*coordPartial 1 (directedWeight b lambda I) p| ≤
          (16+2*D*(M+lambda))*E := by
        rw [abs_mul]
        convert mul_le_mul het hws (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2) using 1
        all_goals try with_reducible_and_instances rfl
        ring
      exact hlift hh hNss

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_DirectedDefectCost
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem multiplierProduct_partial_abs_bound
    {A m : Coord → ℝ} {p : Coord} {M V : ℝ}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p)
    (hM : 0 ≤ M) (hV : 0 ≤ V) (hAv : |A p| ≤ M) (hmv : |m p| ≤ V)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M)
    (hmi : ∀ i : Fin 2, |coordPartial i m p| ≤ V) (i : Fin 2) :
    |coordPartial i (fun q => A q*m q) p| ≤ 2*M*V := by
  rw [HessianCalculus.coordPartial_mul_at hA hm i]
  calc
    _ ≤ |coordPartial i A p*m p| + |A p*coordPartial i m p| := abs_add_le _ _
    _ ≤ M*V + M*V := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul (hAi i) hmv (abs_nonneg _) hM)
        ((mul_le_mul_of_nonneg_left (hmi i) (abs_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hAv hV))
    _ = _ := by ring

theorem multiplierCoefficients_abs_bound
    {A B C m n : Coord → ℝ} {p : Coord} {M V : ℝ}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p) (hn : DifferentiableAt ℝ n p)
    (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M)
    (hmv : |m p| ≤ V) (hnv : |n p| ≤ V)
    (hmi : ∀ i : Fin 2, |coordPartial i m p| ≤ V)
    (hni : ∀ i : Fin 2, |coordPartial i n p| ≤ V) :
    |multiplierT B m n p| ≤ (1+M)*V ∧
    |multiplierS A C m n p| ≤ (3*M)*V ∧
    |multiplierJ A B C m n p| ≤ (1+4*M)*V := by
  have hAm := multiplierProduct_partial_abs_bound hA hm hM hV hAv hmv hAi hmi
  have hAn := multiplierProduct_partial_abs_bound hA hn hM hV hAv hnv hAi hni
  have hprod {a b : ℝ} (ha : |a| ≤ M) (hb : |b| ≤ V) : |a*b| ≤ M*V := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hM
  have hbn := hprod hBv hnv
  have hbm := hprod hBv hmv
  have hcm := hprod hCv hmv
  have hcn := hprod hCv hnv
  refine ⟨?_, ?_, ?_⟩
  · unfold multiplierT
    have hdiff : |coordPartial 1 m p - coordPartial 0 n p| ≤ 2*V :=
      (abs_sub _ _).trans (by linarith [hmi 1, hni 0])
    have hhalf : |(coordPartial 1 m p-coordPartial 0 n p)/2| ≤ V := by
      rw [abs_div]
      norm_num
      linarith
    exact (abs_add_le _ _).trans (by nlinarith only [hhalf, hbn])
  · unfold multiplierS
    have h1 : |-coordPartial 1 (fun q => A q*m q) p/2| ≤ M*V := by
      rw [abs_div, abs_neg]
      norm_num
      linarith [hAm 1]
    have h2 : |coordPartial 0 (fun q => A q*n q) p/2| ≤ M*V := by
      rw [abs_div]
      norm_num
      linarith [hAn 0]
    calc
      _ ≤ |-coordPartial 1 (fun q => A q*m q) p/2 +
          coordPartial 0 (fun q => A q*n q) p/2| + |C p*m p| := abs_add_le _ _
      _ ≤ (|-coordPartial 1 (fun q => A q*m q) p/2| +
          |coordPartial 0 (fun q => A q*n q) p/2|) + |C p*m p| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by nlinarith only [h1, h2, hcm]
  · unfold multiplierJ
    calc
      _ ≤ |-coordPartial 0 m p + B p*m p - coordPartial 1 (fun q => A q*n q) p| +
          |C p*n p| := abs_add_le _ _
      _ ≤ (|-coordPartial 0 m p+B p*m p| + |coordPartial 1 (fun q => A q*n q) p|) +
          |C p*n p| := add_le_add (abs_sub _ _) le_rfl
      _ ≤ ((|-coordPartial 0 m p|+|B p*m p|) + |coordPartial 1 (fun q => A q*n q) p|) +
          |C p*n p| := add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ _ := by rw [abs_neg]; nlinarith only [hmi 0, hbm, hAn 1, hcn]

theorem multiplierQuadratic_abs_bound
    {A B C m n u : Coord → ℝ} {p : Coord} {M V : ℝ}
    (hA : DifferentiableAt ℝ A p) (hm : DifferentiableAt ℝ m p) (hn : DifferentiableAt ℝ n p)
    (hM : 0 ≤ M) (hV : 0 ≤ V)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M)
    (hmv : |m p| ≤ V) (hnv : |n p| ≤ V)
    (hmi : ∀ i : Fin 2, |coordPartial i m p| ≤ V)
    (hni : ∀ i : Fin 2, |coordPartial i n p| ≤ V) :
    |multiplierQuadratic A B C m n u p| ≤
      (2+8*M)*V*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) := by
  obtain ⟨hT,hS,hJ⟩ := multiplierCoefficients_abs_bound hA hm hn hM hV hAv hBv hCv hAi hmv hnv hmi hni
  have hh := scalarQuadratic_abs_bound (x := coordPartial 0 u p) (y := coordPartial 1 u p) hT hJ hS
  have heq : multiplierQuadratic A B C m n u p =
      multiplierT B m n p*(coordPartial 0 u p)^2 +
      multiplierJ A B C m n p*(coordPartial 0 u p*coordPartial 1 u p) +
      multiplierS A C m n p*(coordPartial 1 u p)^2 := by unfold multiplierQuadratic; ring
  rw [heq]
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem directedQuadratic_abs_le_seven
    {A B C I u : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M : ℝ}
    (hA : DifferentiableAt ℝ A p) (hId : DifferentiableAt ℝ I p)
    (hlambda : 0 ≤ lambda) (hM : 0 ≤ M)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ 2)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M) :
    |multiplierQuadratic A B C (directedM b lambda I) (directedN b lambda epsilon I) u p| ≤
      directedQuadraticCostConstant D M lambda S MI * weightedGradient b u p := by
  obtain ⟨hmv,hnv,hmi,hni⟩ := directedMultiplier_firstJet_abs_le_seven
    hId hlambda hM heps heps1 ht hd hdD hs hIv hIi
  have hD : 0 ≤ D := hd.trans hdD
  have hN := (directedWeightJetBudget_bounds hD hM hlambda).1
  have hV : 0 ≤ directedWeightJetBudget D M lambda*Real.exp (lambda*S+MI)*edgeDistance b p^7 := by
    positivity
  have hh := multiplierQuadratic_abs_bound (u := u) hA
    (directedM_differentiableAt b lambda hId) (directedN_differentiableAt b lambda epsilon hId)
    hM hV hAv hBv hCv hAi hmv hnv hmi hni
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  unfold directedQuadraticCostConstant weightedGradient
  ring

theorem directedCoercivityDefect_le_seven
    {A B C chi I u : Coord → ℝ} {p : Coord} {b lambda epsilon D S MI M c2 : ℝ}
    (hA : DifferentiableAt ℝ A p) (hId : DifferentiableAt ℝ I p)
    (hlambda : 0 ≤ lambda) (hM : 0 ≤ M) (hc2 : 0 ≤ c2)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1) (ht : |p 0| ≤ 2)
    (hd : 0 ≤ edgeDistance b p) (hdD : edgeDistance b p ≤ D)
    (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hAv : |A p| ≤ M) (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hAi : ∀ i : Fin 2, |coordPartial i A p| ≤ M) (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤
      directedDefectCostConstant D M lambda S MI c2 * weightedGradient b u p := by
  have hQ := directedQuadratic_abs_le_seven (u := u) hA hId hlambda hM heps heps1 ht hd hdD
    hs hIv hIi hAv hBv hCv hAi
  have hW := directedWeight_le_seven hlambda hd hdD hs hIv
  have hW0 : 0 ≤ directedWeight b lambda I p := by unfold directedWeight; positivity
  have hE : 0 ≤ (coordPartial 0 u p)^2+(coordPartial 1 u p)^2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hc2) hE
  have hbase := nonnegative_cutoff_defect_bound
    (q := multiplierQuadratic A B C (directedM b lambda I) (directedN b lambda epsilon I) u p)
    hchi (mul_nonneg (mul_nonneg hc2 hW0) hE)
  change directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ _ at hbase
  exact hbase.trans (by
    have hh := add_le_add hfirst hQ
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    unfold directedDefectCostConstant weightedGradient
    ring)

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

theorem ellipticWeightC1_energy_nonneg
    {b c glow : ℝ} {chi K G1 u : Coord → ℝ} {p : Coord}
    (hc : 0 < c) (hg : 0 < glow) (hG1 : glow ≤ G1 p) (hp : p 1 ≤ b) :
    0 ≤ ellipticEnergy (fun q => G1 q*K q) (ellipticWeightC1 b c chi K) u p := by
  apply ellipticEnergy_nonneg _ _ _ p (ellipticWeightC1_nonneg _ _ _ _ _)
  intro hv
  have hplt : p 1 < b := by
    by_contra h
    have heq : p 1 = b := le_antisymm hp (le_of_not_gt h)
    rw [ellipticWeightC1_zero heq.ge] at hv
    exact (lt_irrefl (0 : ℝ)) hv
  have hvraw : 0 < ellipticWeight b c chi K p := by
    simpa only [ellipticWeightC1_eq hp] using hv
  have hk := ellipticWeight_pos_implies_curvature hc hplt hvraw
  have hKpos : 0 < K p := (mul_pos (by positivity : 0 < c/2) (sub_pos.mpr hplt)).trans hk
  exact mul_pos (hg.trans_le hG1) hKpos

theorem directedCostConstants_nonneg {D M lambda S MI X c2 : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hlambda : 0 ≤ lambda) (hX : 0 ≤ X) (hc2 : 0 ≤ c2) :
    0 ≤ directedFluxCostConstant D M lambda S MI X ∧
    0 ≤ directedDefectCostConstant D M lambda S MI c2 := by
  have hN := (directedWeightJetBudget_bounds hD hM hlambda).1
  constructor
  · unfold directedFluxCostConstant
    positivity
  · unfold directedDefectCostConstant directedQuadraticCostConstant
    positivity

end SmoothLocal.Weighted

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.Weighted SmoothLocal.Model

theorem actual_cap_directed_costs_le_elliptic
    {g0 eta : MetricField} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    {L R A0 b kappa c1 c2 D glow lambda epsilon S MI M : ℝ}
    {G1 B C I u : Coord → ℝ} {p : Coord}
    (hL : -2 < L) (hR : R < 2) (hA0 : -2 < A0)
    (hk : 0 < kappa) (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hg : 0 < glow)
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hlambda : 0 ≤ lambda)
    (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1)
    (hbackground : ∀ q ∈ U, gaussianCurvature g0 q = modelCurvature kappa q)
    (hsupport : tsupport eta ⊆ patchBox) (hpU : capChart Y p ∈ U)
    (hdisp : |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50)
    (hbelow : p 1 ≤ b) (hdD : edgeDistance b p ≤ D)
    (ht : |p 0| ≤ 2) (hs : |p 1| ≤ S) (hIv : |I p| ≤ MI)
    (hId : DifferentiableAt ℝ I p) (hIi : ∀ i : Fin 2, |coordPartial i I p| ≤ M)
    (hG1 : glow ≤ G1 p)
    (hAd : DifferentiableAt ℝ (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) p)
    (hAv : |G1 p*capPullback Y (gaussianCurvature (g0+eta)) p| ≤ M)
    (hAi : ∀ i : Fin 2,
      |coordPartial i (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) p| ≤ M)
    (hBv : |B p| ≤ M) (hCv : |C p| ≤ M)
    (hcoercive : capPullback Y (gaussianCurvature (g0+eta)) p ≤ c1*edgeDistance b p →
      c2*directedWeight b lambda I p*((coordPartial 0 u p)^2+(coordPartial 1 u p)^2) ≤
        multiplierQuadratic (fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q) B C
          (directedM b lambda I) (directedN b lambda epsilon I) u p) :
    let A := fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q
    let chi := capSpatialCutoff L R A0
    let c := capOverlapThreshold kappa c1 D
    let X := capSpatialDerivativeConstant L R A0
    |directedCutoffError A chi I u b lambda epsilon p| +
      directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤
      (directedFluxCostConstant D M lambda S MI X + directedDefectCostConstant D M lambda S MI c2)*
        (D+1/(glow*c))*
          ellipticEnergy A (ellipticWeightC1 b c (capOuterSpatialCutoff L R A0)
            (capPullback Y (gaussianCurvature (g0+eta)))) u p := by
  let A := fun q => G1 q*capPullback Y (gaussianCurvature (g0+eta)) q
  let K := capPullback Y (gaussianCurvature (g0+eta))
  let chi := capSpatialCutoff L R A0
  let c := capOverlapThreshold kappa c1 D
  let X := capSpatialDerivativeConstant L R A0
  let E := ellipticEnergy A (ellipticWeightC1 b c (capOuterSpatialCutoff L R A0) K) u p
  let CE := D+1/(glow*c)
  let CF := directedFluxCostConstant D M lambda S MI X
  let CD := directedDefectCostConstant D M lambda S MI c2
  change |directedCutoffError A chi I u b lambda epsilon p| +
    directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ (CF+CD)*CE*E
  have hc : 0 < c := capOverlapThreshold_pos hk hc1 hD
  have hX : 0 ≤ X := (abs_nonneg _).trans (capSpatialCutoff_partial_uniform hL hR hA0 p 0)
  have hEnonneg : 0 ≤ E := ellipticWeightC1_energy_nonneg hc hg hG1 hbelow
  have hCE : 0 ≤ CE := by dsimp only [CE] <;> positivity
  have hconst := directedCostConstants_nonneg (S := S) (MI := MI) hD hM hlambda hX hc2
  have hCF : 0 ≤ CF := hconst.1
  have hCD : 0 ≤ CD := hconst.2
  have hd : 0 ≤ edgeDistance b p := sub_nonneg.mpr hbelow
  have hfluxcost : |directedCutoffError A chi I u b lambda epsilon p| ≤ CF*weightedGradient b u p :=
    directedCutoffError_abs_le_seven hlambda heps heps1 ht hd hdD hs hIv hAv
      (capSpatialCutoff_partial_uniform hL hR hA0 p)
  have hdefcost : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ CD*weightedGradient b u p :=
    directedCoercivityDefect_le_seven hAd hId hlambda hM hc2 heps heps1 ht hd hdD hs hIv hIi
      hAv hBv hCv hAi (capSpatialCutoff_range L R A0 p)
  by_cases hedge : p 1 < b
  · have hdpos : 0 < edgeDistance b p := sub_pos.mpr hedge
    have hflux : |directedCutoffError A chi I u b lambda epsilon p| ≤ CF*CE*E := by
      by_cases hz : directedCutoffError A chi I u b lambda epsilon p = 0
      · rw [hz, abs_zero]
        positivity
      · have hder : ∃ i : Fin 2, coordPartial i chi p ≠ 0 := by
          by_contra h
          have hh : ∀ i : Fin 2, coordPartial i chi p = 0 := by
            intro i
            by_contra hi
            exact h ⟨i,hi⟩
          exact hz (multiplierCutoffError_zero A chi (directedM b lambda I)
            (directedN b lambda epsilon I) u p (hh 0) (hh 1))
        obtain ⟨i,hi⟩ := hder
        have hgrad : weightedGradient b u p ≤ CE*E :=
          capOuterElliptic_gradient_on_actual_cutoff_support hL hR hA0 hk hc1 hD hg
            hbackground hsupport hpU hdisp hdpos hdD hG1 hi
        exact hfluxcost.trans (by
          have hh := mul_le_mul_of_nonneg_left hgrad hCF
          convert hh using 1
          all_goals try with_reducible_and_instances rfl
          ring)
    have hdef : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p ≤ CD*CE*E := by
      by_cases hz : directedCoercivityDefect A B C chi I u b lambda epsilon c2 p = 0
      · rw [hz]
        positivity
      · have hgrad : weightedGradient b u p ≤ CE*E :=
          capOuterElliptic_gradient_on_defect hL hR hA0 hk hc1 hD hg hdpos hdD hG1 hcoercive hz
        exact hdefcost.trans (by
          have hh := mul_le_mul_of_nonneg_left hgrad hCD
          convert hh using 1
          all_goals try with_reducible_and_instances rfl
          ring)
    have hh := add_le_add hflux hdef
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have heq : p 1 = b := le_antisymm hbelow (le_of_not_gt hedge)
    rw [directedCutoffError_edge_zero A chi I u b lambda epsilon p heq,
      directedCoercivityDefect_edge_zero A B C chi I u b lambda epsilon c2 p hAd hId heq,
      abs_zero, zero_add]
    positivity

end SmoothLocal.Flow

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

theorem capOuterSpatialCutoff_eq_threeEdge (L R A : ℝ) :
    capOuterSpatialCutoff L R A =
      threeEdgeCutoff (capOuterLeft L) (capOuterLeftOne L) (capOuterRightOne R)
        (capOuterRight R) (capOuterBottom A) (capOuterBottomOne A) := by
  simp only [capOuterSpatialCutoff, capSpatialCutoff, neg_neg, capOuterLeft, capOuterLeftOne,
    capOuterRightOne, capOuterRight, capOuterBottom, capOuterBottomOne]

theorem capOuterRectangle_subset_domain {L R A b : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (hb : b < 2) :
    closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A) b ⊆ capChartDomain := by
  obtain ⟨hlo,hli,hlu,hri,hrr,hro,hao,hai,hau,hlx,hrx⟩ := capOuterRectangle_edges hL hR hA
  intro p hp
  exact ⟨⟨hlo.trans_le hp.1.1, hp.1.2.trans_lt hro⟩,
    ⟨hao.trans_le hp.2.1,hp.2.2.trans_lt hb⟩⟩

theorem capSpatialCutoff_outer_boundary {L R A b : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) :
    (∀ s ∈ Icc (capOuterBottom A) b,
      capSpatialCutoff L R A (boxPoint (capOuterLeft L) s) = 0 ∧
      capSpatialCutoff L R A (boxPoint (capOuterRight R) s) = 0) ∧
    (∀ t ∈ Icc (capOuterLeft L) (capOuterRight R),
      capSpatialCutoff L R A (boxPoint t (capOuterBottom A)) = 0) := by
  obtain ⟨hlo,hli,hlu,hlx⟩ := capEdges_bounds hL
  obtain ⟨hro,hri,hru,hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao,hai,hau,hax⟩ := capEdges_bounds hA
  have hlout : capOuterLeft L < capOuterEdge L := by
    have hh := capEdges_bounds hlo
    exact hh.2.1.trans hh.2.2.2
  have hrout : -capOuterEdge (-R) < capOuterRight R := by
    have hh := capEdges_bounds hro
    exact neg_lt_neg (hh.2.1.trans hh.2.2.2)
  have haout : capOuterBottom A < capOuterEdge A := by
    have hh := capEdges_bounds hao
    exact hh.2.1.trans hh.2.2.2
  constructor
  · intro s hs
    constructor
    · apply threeEdgeCutoff_zero hli (neg_lt_neg hri) hai
      exact Or.inl (by simpa [boxPoint] using hlout.le)
    · apply threeEdgeCutoff_zero hli (neg_lt_neg hri) hai
      exact Or.inr (Or.inl (by simpa [boxPoint] using hrout.le))
  · intro t ht
    apply threeEdgeCutoff_zero hli (neg_lt_neg hri) hai
    exact Or.inr (Or.inr (by simpa [boxPoint] using haout.le))

end SmoothLocal.Weighted

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_NormedCoordinateCalculus
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Geometry
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {F : Coord → V} {U : Set Coord} {p : Coord}

theorem normed_coordPartial_contDiffOn (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (i : Fin 2) :
    ContDiffOn ℝ ∞ (coordPartial i F) U :=
  (hF.fderiv_of_isOpen hU (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffOn_const

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Coordinates_AffinePushforward
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Geometry

def affineInverseCoordinates (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (p : Coord) : Coord := R⁻¹ *ᵥ (p - b)

theorem affineInverseCoordinates_contDiff (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) :
    ContDiff ℝ ∞ (affineInverseCoordinates b R) :=
  (matrixContinuousLinear R⁻¹).contDiff.comp (contDiff_id.sub contDiff_const)

theorem affineInverseCoordinates_affineCoordinates (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) (q : Coord) :
    affineInverseCoordinates b R (affineCoordinates b R q) = q := by
  have hSR := Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  simp only [affineInverseCoordinates, affineCoordinates, add_sub_cancel_left, Matrix.mulVec_mulVec, hSR, Matrix.one_mulVec]

theorem affineCoordinates_affineInverseCoordinates (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) (p : Coord) :
    affineCoordinates b R (affineInverseCoordinates b R p) = p := by
  have hRS := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  simp only [affineInverseCoordinates, affineCoordinates, Matrix.mulVec_mulVec, hRS, Matrix.one_mulVec, add_sub_cancel]

def affineCoordinateHomeomorph (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hR : IsUnit R) : Coord ≃ₜ Coord where
  toFun := affineCoordinates b R
  invFun := affineInverseCoordinates b R
  left_inv := affineInverseCoordinates_affineCoordinates b R hR
  right_inv := affineCoordinates_affineInverseCoordinates b R hR
  continuous_toFun := (affineCoordinates_contDiff b R).continuous
  continuous_invFun := (affineInverseCoordinates_contDiff b R).continuous

def affinePushforwardMetric (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) : MetricField := fun p =>
  R⁻¹ᵀ * η (affineInverseCoordinates b R p) * R⁻¹

theorem affinePullback_pushforward (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    affinePullbackMetric (affinePushforwardMetric η b R) b R = η := by
  have hSR := Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det _).mp hR)
  have hT : Rᵀ * R⁻¹ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hSR, Matrix.transpose_one]
  funext q
  simp only [affinePullbackMetric, affinePushforwardMetric,
    affineInverseCoordinates_affineCoordinates b R hR]
  calc
    _ = (Rᵀ * R⁻¹ᵀ) * η q * (R⁻¹ * R) := by simp only [Matrix.mul_assoc]
    _ = η q := by rw [hT, hSR, Matrix.one_mul, Matrix.mul_one]

theorem affinePullbackMetric_add (g η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) :
    affinePullbackMetric (g + η) b R =
      affinePullbackMetric g b R + affinePullbackMetric η b R := by
  funext p
  simp only [affinePullbackMetric, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]

theorem affinePushforwardMetric_eq_zero_iff (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) (p : Coord) :
    affinePushforwardMetric η b R p = 0 ↔ η (affineInverseCoordinates b R p) = 0 := by
  constructor
  · intro hp
    have h := congrFun (affinePullback_pushforward η b R hR)
      (affineInverseCoordinates b R p)
    simp only [affinePullbackMetric, affineCoordinates_affineInverseCoordinates b R hR,
      hp, Matrix.mul_zero, Matrix.zero_mul] at h
    exact h.symm
  · intro hp
    simp only [affinePushforwardMetric, hp, Matrix.mul_zero, Matrix.zero_mul]

theorem affinePushforwardMetric_support (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    Function.support (affinePushforwardMetric η b R) =
      affineCoordinates b R '' Function.support η := by
  ext p
  constructor
  · intro hp
    refine ⟨affineInverseCoordinates b R p, ?_,
      affineCoordinates_affineInverseCoordinates b R hR p⟩
    change η (affineInverseCoordinates b R p) ≠ 0
    intro hη
    exact hp ((affinePushforwardMetric_eq_zero_iff η b R hR p).mpr hη)
  · rintro ⟨q, hq, rfl⟩
    change affinePushforwardMetric η b R (affineCoordinates b R q) ≠ 0
    intro hη
    have hzero := (affinePushforwardMetric_eq_zero_iff η b R hR _).mp hη
    rw [affineInverseCoordinates_affineCoordinates b R hR] at hzero
    exact hq hzero

theorem affinePushforwardMetric_tsupport (η : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R) :
    tsupport (affinePushforwardMetric η b R) = affineCoordinates b R '' tsupport η := by
  rw [tsupport, affinePushforwardMetric_support η b R hR]
  exact ((affineCoordinateHomeomorph b R hR).image_closure (Function.support η)).symm

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Curvature_AffineCurvature
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology BigOperators Matrix
open Filter

namespace SmoothLocal.Geometry

namespace AffineCalculus

theorem coordPartial_sum_const_mul (f : Fin 2 → Coord → ℝ) (c : Fin 2 → ℝ)
    {p : Coord} (hf : ∀ a, DifferentiableAt ℝ (f a) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, c a * f a q) p =
      ∑ a, c a * coordPartial i (f a) p := by
  rw [HessianCalculus.coordPartial_sum_two _ (fun a => (hf a).const_mul (c a)) i]
  apply Finset.sum_congr rfl
  intro a _
  exact coordPartial_const_mul_at (hf a) (c a) i

theorem coordPartial_double_sum_const_mul
    (f : Fin 2 → Fin 2 → Coord → ℝ) (c : Fin 2 → Fin 2 → ℝ)
    {p : Coord} (hf : ∀ a b, DifferentiableAt ℝ (f a b) p) (i : Fin 2) :
    coordPartial i (fun q => ∑ a, ∑ b, c a b * f a b q) p =
      ∑ a, ∑ b, c a b * coordPartial i (f a b) p := by
  rw [HessianCalculus.coordPartial_sum_two _
    (fun a => DifferentiableAt.fun_sum fun b _ => (hf a b).const_mul (c a b)) i]
  apply Finset.sum_congr rfl
  intro a _
  exact coordPartial_sum_const_mul (f a) (c a) (hf a) i

end AffineCalculus

theorem coordPartial_christoffel_affinePullback_push
    {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a i j k : Fin 2) :
    (∑ l, R a l * coordPartial i (christoffel (affinePullbackMetric g b R) l j k) q) =
      ∑ c, ∑ d, ∑ e, R c j * R d k * R e i *
        coordPartial e (christoffel g a c d) (affineCoordinates b R q) := by
  have hV := isOpen_affine_preimage hU b R
  have hgR := affinePullbackMetric_smoothPositive hg b R
    (Matrix.mulVec_injective_of_isUnit hR)
  have hL (l : Fin 2) : DifferentiableAt ℝ
      (christoffel (affinePullbackMetric g b R) l j k) q :=
    (((christoffel_contDiffOn hgR hV l j k) q hq).contDiffAt
      (hV.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hG (c d : Fin 2) : DifferentiableAt ℝ (christoffel g a c d)
      (affineCoordinates b R q) :=
    (((christoffel_contDiffOn hg hU a c d) _ hq).contDiffAt
      (hU.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hGc (c d : Fin 2) : DifferentiableAt ℝ
      (fun p => christoffel g a c d (affineCoordinates b R p)) q :=
    (hG c d).comp q (affineCoordinates_hasFDerivAt b R q).differentiableAt
  have hchain (c d : Fin 2) :
      coordPartial i (fun p => christoffel g a c d (affineCoordinates b R p)) q =
        ∑ e, R e i * coordPartial e (christoffel g a c d) (affineCoordinates b R q) :=
    coordPartial_affine_comp b R q (hG c d) i
  have heq : (fun p => ∑ l, R a l *
      christoffel (affinePullbackMetric g b R) l j k p) =ᶠ[𝓝 q]
      (fun p => ∑ c, ∑ d, R c j * R d k *
        christoffel g a c d (affineCoordinates b R p)) := by
    filter_upwards [hV.mem_nhds hq] with p hp
    exact christoffel_affinePullback_push hg hU b R hR p hp a j k
  calc
    _ = coordPartial i (fun p => ∑ l, R a l *
        christoffel (affinePullbackMetric g b R) l j k p) q :=
      (AffineCalculus.coordPartial_sum_const_mul _ _ hL i).symm
    _ = coordPartial i (fun p => ∑ c, ∑ d, R c j * R d k *
        christoffel g a c d (affineCoordinates b R p)) q := by
      unfold coordPartial
      rw [heq.fderiv_eq]
    _ = ∑ c, ∑ d, (R c j * R d k) * coordPartial i
        (fun p => christoffel g a c d (affineCoordinates b R p)) q :=
      AffineCalculus.coordPartial_double_sum_const_mul _ _ hGc i
    _ = _ := by
      simp_rw [hchain]
      simp only [Fin.sum_univ_two]
      ring

theorem riemann_affinePullback_push {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (a k i j : Fin 2) :
    (∑ l, R a l * riemann (affinePullbackMetric g b R) l k i j q) =
      ∑ c, ∑ d, ∑ e, R c k * R d i * R e j *
        riemann g a c d e (affineCoordinates b R q) := by
  let C := fun a i j => christoffel (affinePullbackMetric g b R) a i j q
  let D := fun a i j => christoffel g a i j (affineCoordinates b R q)
  have hp (a i j : Fin 2) : (∑ l, R a l * C l i j) =
      ∑ c, ∑ d, R c i * R d j * D a c d :=
    christoffel_affinePullback_push hg hU b R hR q hq a i j
  calc
    _ = (∑ l, R a l * coordPartial i
          (christoffel (affinePullbackMetric g b R) l j k) q) -
        (∑ l, R a l * coordPartial j
          (christoffel (affinePullbackMetric g b R) l i k) q) +
        (∑ l, R a l * ∑ m, C m j k * C l i m) -
        (∑ l, R a l * ∑ m, C m i k * C l j m) := by
      simp only [riemann, C, Fin.sum_univ_two]
      ring
    _ = (∑ c, ∑ d, ∑ e, R c j * R d k * R e i *
          coordPartial e (christoffel g a c d) (affineCoordinates b R q)) -
        (∑ c, ∑ d, ∑ e, R c i * R d k * R e j *
          coordPartial e (christoffel g a c d) (affineCoordinates b R q)) +
        (∑ c, ∑ d, ∑ e, ∑ f, R c i * R e j * R f k * D d e f * D a c d) -
        (∑ c, ∑ d, ∑ e, ∑ f, R c j * R e i * R f k * D d e f * D a c d) := by
      rw [coordPartial_christoffel_affinePullback_push hg hU b R hR q hq a i j k,
        coordPartial_christoffel_affinePullback_push hg hU b R hR q hq a j i k,
        AffineCalculus.pushed_connection_product R C D hp a i j k,
        AffineCalculus.pushed_connection_product R C D hp a j i k]
    _ = _ := by
      simp only [riemann, D, Fin.sum_univ_two]
      ring

theorem loweredRiemann_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) (l k i j : Fin 2) :
    loweredRiemann (affinePullbackMetric g b R) l k i j q =
      ∑ a, ∑ c, ∑ d, ∑ e, R a l * R c k * R d i * R e j *
        loweredRiemann g a c d e (affineCoordinates b R q) := by
  calc
    _ = ∑ a, ∑ c, R a l * g (affineCoordinates b R q) a c *
        (∑ r, R c r * riemann (affinePullbackMetric g b R) r k i j q) := by
      simp only [loweredRiemann, affinePullbackMetric, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_two]
      ring
    _ = ∑ a, ∑ c, R a l * g (affineCoordinates b R q) a c *
        (∑ d, ∑ e, ∑ f, R d k * R e i * R f j *
          riemann g c d e f (affineCoordinates b R q)) := by
      simp_rw [riemann_affinePullback_push hg hU b R hR q hq]
    _ = _ := by simp only [loweredRiemann, Fin.sum_univ_two] <;> ring

theorem gaussianCurvature_affinePullback {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : IsUnit R)
    (q : Coord) (hq : affineCoordinates b R q ∈ U) :
    gaussianCurvature (affinePullbackMetric g b R) q =
      gaussianCurvature g (affineCoordinates b R q) := by
  have hgR := affinePullbackMetric_smoothPositive hg b R
    (Matrix.mulVec_injective_of_isUnit hR)
  have hsym : g (affineCoordinates b R q) 1 0 = g (affineCoordinates b R q) 0 1 :=
    metric_coeff_symm hg hq 1 0
  have hlow : loweredRiemann (affinePullbackMetric g b R) 0 1 0 1 q =
      gaussianCurvature g (affineCoordinates b R q) * (affinePullbackMetric g b R q).det := by
    rw [loweredRiemann_affinePullback hg hU b R hR q hq]
    simp only [loweredRiemann_factorization hg hU hq,
      affinePullbackMetric, Matrix.det_fin_two, Matrix.mul_apply,
      Matrix.transpose_apply, Fin.sum_univ_two, hsym]
    ring
  change loweredRiemann (affinePullbackMetric g b R) 0 1 0 1 q /
    (affinePullbackMetric g b R q).det = _
  rw [hlow, mul_div_cancel_right₀ _ (metricDet_ne_zero hgR hq)]

theorem det_affinePullbackMetric (g : MetricField) (b : Coord)
    (R : Matrix (Fin 2) (Fin 2) ℝ) (q : Coord) :
    (affinePullbackMetric g b R q).det =
      R.det ^ 2 * (g (affineCoordinates b R q)).det := by
  simp only [affinePullbackMetric, Matrix.det_mul, Matrix.det_transpose]
  ring

end SmoothLocal.Geometry

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapReflectionGeometry
attribute [-simp] _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter
open scoped ContDiff Topology Matrix

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Model

def reflectPoint (p : Coord) : Coord := fun i => if i = 0 then p 0 else -p 1

@[simp] theorem reflectPoint_zero (p : Coord) : reflectPoint p 0 = p 0 := by
  simp [reflectPoint]

@[simp] theorem reflectPoint_one (p : Coord) : reflectPoint p 1 = -p 1 := by
  simp [reflectPoint]

@[simp] theorem reflectPoint_twice (p : Coord) : reflectPoint (reflectPoint p) = p := by
  ext i
  fin_cases i <;> simp

theorem reflectPoint_eq_affine : reflectPoint = affineCoordinates 0 reflectionMatrix := by
  funext p
  ext i
  fin_cases i <;> simp [reflectPoint,affineCoordinates,reflectionMatrix,
    dotProduct,Fin.sum_univ_two]

theorem reflectPoint_contDiff : ContDiff ℝ ∞ reflectPoint := by
  rw [reflectPoint_eq_affine]
  exact affineCoordinates_contDiff 0 reflectionMatrix

def reflectionIsometry : Coord ≃ₗᵢ[ℝ] Coord where
  toFun := reflectPoint
  invFun := reflectPoint
  left_inv := reflectPoint_twice
  right_inv := reflectPoint_twice
  map_add' p q := by
    ext i
    fin_cases i <;> simp [reflectPoint,Pi.add_apply,add_comm]
  map_smul' a p := by
    ext i
    fin_cases i <;> simp [reflectPoint,Pi.smul_apply,smul_eq_mul]
  norm_map' p := by
    change ‖reflectPoint p‖ = ‖p‖
    rw [Pi.norm_def,Pi.norm_def]
    congr 1
    apply Finset.sup_congr rfl
    intro index _
    fin_cases index <;> simp

def reflectedScalar {V : Type*} (f : Coord → V) : Coord → V := f ∘ reflectPoint

def reflectedMetric (g : MetricField) : MetricField :=
  affinePullbackMetric g 0 reflectionMatrix

theorem reflectedScalar_contDiffOn
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : Coord → V} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (reflectedScalar f) (reflectPoint ⁻¹' U) :=
  hf.comp reflectPoint_contDiff.contDiffOn (fun _ hp => hp)

theorem reflectedDomain_isOpen {U : Set Coord} (hU : IsOpen U) :
    IsOpen (reflectPoint ⁻¹' U) := hU.preimage reflectPoint_contDiff.continuous

theorem reflectedMetric_smoothPositive {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) :
    SmoothPositiveOn (reflectedMetric g) (reflectPoint ⁻¹' U) := by
  simpa only [reflectedMetric,reflectPoint_eq_affine] using
    affinePullbackMetric_smoothPositive hg 0 reflectionMatrix
      (Matrix.mulVec_injective_of_isUnit reflectionMatrix_isUnit)

theorem reflectedMetric_add (g eta : MetricField) :
    reflectedMetric (g+eta) = reflectedMetric g + reflectedMetric eta :=
  affinePullbackMetric_add g eta 0 reflectionMatrix

theorem reflectedMetric_entry (g : MetricField) (p : Coord) (i j : Fin 2) :
    reflectedMetric g p i j =
      if i=j then g (reflectPoint p) i j else -g (reflectPoint p) i j := by
  rw [reflectPoint_eq_affine]
  fin_cases i <;> fin_cases j <;>
    simp [reflectedMetric,affinePullbackMetric,reflectionMatrix,Matrix.mul_apply,
      Matrix.transpose_apply,Fin.sum_univ_two]

theorem reflectedMetric_det (g : MetricField) (p : Coord) :
    (reflectedMetric g p).det = (g (reflectPoint p)).det := by
  simpa only [reflectedMetric,reflectPoint_eq_affine,reflectionMatrix_det,
    neg_one_sq,one_mul] using det_affinePullbackMetric g 0 reflectionMatrix p

theorem reflectedMetric_curvature {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {p : Coord} (hp : reflectPoint p ∈ U) :
    gaussianCurvature (reflectedMetric g) p = gaussianCurvature g (reflectPoint p) := by
  simpa only [reflectedMetric,reflectPoint_eq_affine] using
    gaussianCurvature_affinePullback hg hU 0 reflectionMatrix reflectionMatrix_isUnit p
      (by simpa only [←reflectPoint_eq_affine] using hp)

theorem reflectedMetric_hessian {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    covHessian (reflectedMetric g) (reflectedScalar z) p =
      reflectionMatrixᵀ * covHessian g z (reflectPoint p) * reflectionMatrix := by
  simpa only [reflectedMetric,reflectedScalar,reflectPoint_eq_affine] using
    covHessian_affinePullback hg hz hU 0 reflectionMatrix reflectionMatrix_isUnit p
      (by simpa only [←reflectPoint_eq_affine] using hp)

theorem reflectedMetric_hessian_entry {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) (i j : Fin 2) :
    covHessian (reflectedMetric g) (reflectedScalar z) p i j =
      if i=j then covHessian g z (reflectPoint p) i j
      else -covHessian g z (reflectPoint p) i j := by
  rw [reflectedMetric_hessian hg hz hU hp]
  fin_cases i <;> fin_cases j <;>
    simp [reflectionMatrix,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]

theorem reflectedMetric_hessian_det {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    (covHessian (reflectedMetric g) (reflectedScalar z) p).det =
      (covHessian g z (reflectPoint p)).det := by
  rw [reflectedMetric_hessian hg hz hU hp]
  simp [Matrix.det_mul,Matrix.det_transpose]

theorem reflectedMetric_energy {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    heightEnergy (reflectedMetric g) (reflectedScalar z) p = heightEnergy g z (reflectPoint p) := by
  have hd := (hz.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  simpa only [reflectedMetric,reflectedScalar,reflectPoint_eq_affine,reflectionMatrix_det,
    neg_one_sq,one_mul] using
    heightEnergy_affinePullback (g := g) 0 reflectionMatrix reflectionMatrix_isUnit p
      (by simpa only [←reflectPoint_eq_affine] using hd)

theorem reflectedMetric_quotient {g : MetricField} {z : Coord → ℝ} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    {p : Coord} (hp : reflectPoint p ∈ U) :
    hessianQuotient (reflectedMetric g) (reflectedScalar z) p =
      -hessianQuotient g z (reflectPoint p) := by
  simp only [hessianQuotient,reflectedMetric_hessian_entry hg hz hU hp,
    show (0 : Fin 2) ≠ 1 by decide,ite_false, if_false,ite_true, if_true,neg_div]

theorem reflectPoint_mem_symmetricSquare (r : ℝ) (p : Coord) :
    reflectPoint p ∈ Icc (fun _ : Fin 2 => -r) (fun _ => r) ↔
      p ∈ Icc (fun _ : Fin 2 => -r) (fun _ => r) := by
  simp only [mem_Icc,Pi.le_def,Fin.forall_fin_two,reflectPoint_zero,reflectPoint_one]
  constructor <;> rintro ⟨⟨h0,h1⟩,⟨h2,h3⟩⟩ <;> constructor <;> constructor <;> linarith

theorem reflectPoint_mem_modelSquare (p : Coord) :
    reflectPoint p ∈ modelSquare ↔ p ∈ modelSquare := reflectPoint_mem_symmetricSquare 3 p

theorem reflectedDomain_contains_modelSquare {U : Set Coord} (hS : modelSquare ⊆ U) :
    modelSquare ⊆ reflectPoint ⁻¹' U := by
  intro p hp
  exact hS ((reflectPoint_mem_modelSquare p).mpr hp)

theorem modelCurvature_reflect (kappa : ℝ) (p : Coord) :
    modelCurvature kappa (reflectPoint p) = modelCurvature kappa p := by
  simp only [modelCurvature,reflectPoint_zero,reflectPoint_one]
  rw [modelProfile_even (p 1)]

theorem reflectedMetric_model {g0 : MetricField} {U : Set Coord} {kappa : ℝ}
    (hg0 : SmoothPositiveOn g0 U) (hU : IsOpen U)
    (hmodel : ∀ p ∈ U, gaussianCurvature g0 p = modelCurvature kappa p) :
    ∀ p ∈ reflectPoint ⁻¹' U,
      gaussianCurvature (reflectedMetric g0) p = modelCurvature kappa p := by
  intro p hp
  rw [reflectedMetric_curvature hg0 hU hp,hmodel _ hp,modelCurvature_reflect]

theorem reflectedMetric_eq_pushforward (g : MetricField) :
    reflectedMetric g = affinePushforwardMetric g 0 reflectionMatrix := by
  funext p
  simp only [reflectedMetric,affinePullbackMetric,affinePushforwardMetric,
    affineInverseCoordinates,affineCoordinates,reflectionMatrix_inv,sub_zero,zero_add]

theorem reflectedMetric_tsupport (g : MetricField) :
    tsupport (reflectedMetric g) = reflectPoint '' tsupport g := by
  rw [reflectedMetric_eq_pushforward,reflectPoint_eq_affine]
  exact affinePushforwardMetric_tsupport g 0 reflectionMatrix reflectionMatrix_isUnit

theorem reflectedMetric_support_patch {eta : MetricField} (h : tsupport eta ⊆ patchBox) :
    tsupport (reflectedMetric eta) ⊆ patchBox := by
  rw [reflectedMetric_tsupport]
  rintro p ⟨q,hq,rfl⟩
  exact (reflectPoint_mem_symmetricSquare (1/10) q).mpr (h hq)

theorem reflectedScalar_jet_norm
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : Coord → V) (p : Coord) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (reflectedScalar f) p‖ =
      ‖iteratedFDeriv ℝ k f (reflectPoint p)‖ :=
  reflectionIsometry.norm_iteratedFDeriv_comp_right f p k

theorem reflectedMetric_entry_jet_norm (g : MetricField) (p : Coord)
    (i j : Fin 2) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q => reflectedMetric g q i j) p‖ =
      ‖iteratedFDeriv ℝ k (fun q => g q i j) (reflectPoint p)‖ := by
  have he : (fun q => reflectedMetric g q i j) =
      if i=j then reflectedScalar (fun q => g q i j)
      else -reflectedScalar (fun q => g q i j) := by
    funext q
    rw [reflectedMetric_entry]
    split_ifs <;> rfl
  rw [he]
  split_ifs
  · exact reflectedScalar_jet_norm _ p k
  · rw [iteratedFDeriv_neg_apply,norm_neg]
    exact reflectedScalar_jet_norm _ p k

theorem reflectedScalar_C8 {z : Coord → ℝ} {Z : ℝ}
    (hZ : ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) :
    ∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k (reflectedScalar z) p‖ ≤ Z := by
  intro k hk p hp
  rw [reflectedScalar_jet_norm]
  exact hZ k hk _ ((reflectPoint_mem_modelSquare p).mpr hp)

theorem reflectedMetric_C8 {g : MetricField} {G : ℝ}
    (hG : ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) :
    ∀ i j : Fin 2, ∀ k ≤ 8, ∀ p ∈ modelSquare,
      ‖iteratedFDeriv ℝ k (fun q => reflectedMetric g q i j) p‖ ≤ G := by
  intro i j k hk p hp
  rw [reflectedMetric_entry_jet_norm]
  exact hG i j k hk _ ((reflectPoint_mem_modelSquare p).mpr hp)

end SmoothLocal.Flow.Reflection

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

theorem square_difference_le_interval_energy
    {f df : ℝ → ℝ} {a b x v : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t)
    (hx : x ∈ Icc a b) (hv : v ∈ Icc a b) :
    f x ^ 2 - f v ^ 2 ≤ ∫ t in a..b, (f t ^ 2 + df t ^ 2) := by
  have hsub : uIcc v x ⊆ Icc a b := uIcc_subset_Icc hv hx
  have hsq (t : ℝ) (ht : t ∈ uIcc v x) :
      HasDerivAt (fun r => f r ^ 2) (2 * f t * df t) t := by
    convert (hd t (hsub ht)).pow 2 using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hcd : ContinuousOn (fun t => 2 * f t * df t) (uIcc v x) :=
    ((continuousOn_const.mul hf).mul hdf).mono hsub
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hsq hcd.intervalIntegrable
  have hE : ContinuousOn (fun t => f t ^ 2 + df t ^ 2) (Icc a b) :=
    (hf.pow 2).add (hdf.pow 2)
  have hbound : ∀ᵐ t ∂volume.restrict (uIoc v x),
      ‖2 * f t * df t‖ ≤ f t ^ 2 + df t ^ 2 :=
    Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs] using abs_two_mul_le_squares (f t) (df t))
  have hnorm := intervalIntegral.norm_integral_le_abs_of_norm_le hbound
    ((hE.mono hsub).intervalIntegrable)
  have hu : uIoc v x ⊆ uIoc a b :=
    uIoc_subset_uIoc_of_uIcc_subset_uIcc (by simpa only [uIcc_of_le hab] using hsub)
  have hnonneg : ∀ᵐ t ∂volume.restrict (uIoc a b), 0 ≤ f t ^ 2 + df t ^ 2 :=
    Filter.Eventually.of_forall (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hmono := intervalIntegral.abs_integral_mono_interval hu hnonneg
    (hE.intervalIntegrable_of_Icc hab)
  have hI : 0 ≤ ∫ t in a..b, (f t ^ 2 + df t ^ 2) :=
    intervalIntegral.integral_nonneg_of_forall hab
      (fun t => add_nonneg (sq_nonneg _) (sq_nonneg _))
  rw [hFTC, Real.norm_eq_abs] at hnorm
  rw [abs_of_nonneg hI] at hmono
  exact (le_abs_self _).trans (hnorm.trans hmono)

theorem interval_point_square_bound
    {f df : ℝ → ℝ} {a b x : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Icc a b)) (hdf : ContinuousOn df (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivAt f (df t) t) (hx : x ∈ Icc a b) :
    f x ^ 2 ≤ (1 + 1 / (b - a)) * (∫ t in a..b, f t ^ 2) +
      ∫ t in a..b, df t ^ 2 := by
  let E : ℝ := ∫ t in a..b, (f t ^ 2 + df t ^ 2)
  have hpoint : ∀ v ∈ Icc a b, f x ^ 2 ≤ f v ^ 2 + E := by
    intro v hv
    have h := square_difference_le_interval_energy hab.le hf hdf hd hx hv
    dsimp only [E]
    linarith
  have hfi : IntervalIntegrable (fun t => f t^2) volume a b :=
    (hf.pow 2).intervalIntegrable_of_Icc hab.le
  have hdi : IntervalIntegrable (fun t => df t^2) volume a b :=
    (hdf.pow 2).intervalIntegrable_of_Icc hab.le
  have havg := intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => f x ^ 2) volume a b)
    (hfi.add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add hfi intervalIntegrable_const] at havg
  simp only [intervalIntegral.integral_const, smul_eq_mul] at havg
  have hE : E = (∫ t in a..b, f t ^ 2) + ∫ t in a..b, df t ^ 2 := by
    exact intervalIntegral.integral_add hfi hdi
  rw [hE] at havg
  have hw : 0 < b - a := sub_pos.mpr hab
  have hi : (b - a) * (1 / (b - a)) = 1 := by field_simp [ne_of_gt hw]
  have hiscale := congrArg (fun r : ℝ => r * (∫ t in a..b, f t ^ 2)) hi
  have hscaled : (b - a) * (f x^2) ≤ (b - a) *
      ((1 + 1 / (b - a)) * (∫ t in a..b, f t^2) + ∫ t in a..b, df t^2) := by
    nlinarith only [havg, hiscale]
  exact le_of_mul_le_mul_left hscaled hw

end SmoothLocal.Sobolev

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_RectangleSobolev
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem rectangle_vertical_trace_square_bound
    {F Fs : Coord → ℝ} (ht : tl ≤ tr) (hs : sb < st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st))
    (hFs : ContinuousOn Fs (closedRectangle tl tr sb st))
    (hd : ∀ t ∈ Icc tl tr, ∀ s ∈ Icc sb st,
      HasDerivAt (fun r => F (boxPoint t r)) (Fs (boxPoint t s)) s)
    {y : ℝ} (hy : y ∈ Icc sb st) :
    (∫ t in tl..tr, F (boxPoint t y) ^ 2) ≤
      (1 + 1 / (st - sb)) * rectangleIntegral tl tr sb st (fun p => F p ^ 2) +
        rectangleIntegral tl tr sb st (fun p => Fs p ^ 2) := by
  have hv (t : ℝ) (ht' : t ∈ Icc tl tr) :
      F (boxPoint t y) ^ 2 ≤
      (1 + 1 / (st - sb)) * (∫ s in sb..st, F (boxPoint t s) ^ 2) +
        ∫ s in sb..st, Fs (boxPoint t s) ^ 2 := by
    have hcF : ContinuousOn (fun s => F (boxPoint t s)) (Icc sb st) :=
      hF.comp (by unfold boxPoint; fun_prop) (fun s hs' => boxPoint_mem ht' hs')
    have hcFs : ContinuousOn (fun s => Fs (boxPoint t s)) (Icc sb st) :=
      hFs.comp (by unfold boxPoint; fun_prop) (fun s hs' => boxPoint_mem ht' hs')
    exact interval_point_square_bound hs hcF hcFs (hd t ht') hy
  have hline : ContinuousOn (fun t => F (boxPoint t y) ^ 2) (Icc tl tr) :=
    (hF.pow 2).comp (by unfold boxPoint; fun_prop) (fun t ht' => boxPoint_mem ht' hy)
  have hIF := rectangle_vertical_integral_intervalIntegrable ht hs.le (hF.pow 2)
  have hIS := rectangle_vertical_integral_intervalIntegrable ht hs.le (hFs.pow 2)
  have hi := intervalIntegral.integral_mono_on ht
    (hline.intervalIntegrable_of_Icc ht)
    ((hIF.const_mul (1 + 1 / (st - sb))).add hIS) hv
  rw [intervalIntegral.integral_add (hIF.const_mul (1 + 1 / (st - sb))) hIS,
    intervalIntegral.integral_const_mul] at hi
  rw [← rectangleIntegral_swap ht hs.le (hF.pow 2),
    ← rectangleIntegral_swap ht hs.le (hFs.pow 2)] at hi
  exact hi

theorem rectangle_point_square_bound
    {f : Coord → ℝ} {U : Set Coord} (ht : tl < tr) (hs : sb < st)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (hbox : closedRectangle tl tr sb st ⊆ U)
    {x y : ℝ} (hx : x ∈ Icc tl tr) (hy : y ∈ Icc sb st) :
    f (boxPoint x y) ^ 2 ≤
      (1 + 1 / (tr - tl)) * (1 + 1 / (st - sb)) *
        rectangleIntegral tl tr sb st (fun p => f p ^ 2) +
      (1 + 1 / (st - sb)) *
        rectangleIntegral tl tr sb st (fun p => coordPartial 0 f p ^ 2) +
      (1 + 1 / (tr - tl)) *
        rectangleIntegral tl tr sb st (fun p => coordPartial 1 f p ^ 2) +
      rectangleIntegral tl tr sb st (fun p => coordPartial 1 (coordPartial 0 f) p ^ 2) := by
  have hfx := partial_contDiffOn hf hU 0
  have hfy := partial_contDiffOn hf hU 1
  have hfyx := partial_contDiffOn hfx hU 1
  have hfc : ContinuousOn f (closedRectangle tl tr sb st) := hf.continuousOn.mono hbox
  have hfxc : ContinuousOn (coordPartial 0 f) (closedRectangle tl tr sb st) :=
    hfx.continuousOn.mono hbox
  have hfyc : ContinuousOn (coordPartial 1 f) (closedRectangle tl tr sb st) :=
    hfy.continuousOn.mono hbox
  have hfyxc : ContinuousOn (coordPartial 1 (coordPartial 0 f))
      (closedRectangle tl tr sb st) := hfyx.continuousOn.mono hbox
  have hdt (t : ℝ) (ht' : t ∈ Icc tl tr) :
      HasDerivAt (fun r => f (boxPoint r y)) (coordPartial 0 f (boxPoint t y)) t := by
    have hp := hbox (boxPoint_mem ht' hy)
    exact ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
      |>.comp_hasDerivAt t (boxPoint_hasDerivAt_t t y)
  have hds (t : ℝ) (ht' : t ∈ Icc tl tr) (s : ℝ) (hs' : s ∈ Icc sb st) :
      HasDerivAt (fun r => f (boxPoint t r)) (coordPartial 1 f (boxPoint t s)) s := by
    have hp := hbox (boxPoint_mem ht' hs')
    exact ((hf.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
      |>.comp_hasDerivAt s (boxPoint_hasDerivAt_s t s)
  have hdxs (t : ℝ) (ht' : t ∈ Icc tl tr) (s : ℝ) (hs' : s ∈ Icc sb st) :
      HasDerivAt (fun r => coordPartial 0 f (boxPoint t r))
        (coordPartial 1 (coordPartial 0 f) (boxPoint t s)) s := by
    have hp := hbox (boxPoint_mem ht' hs')
    exact ((hfx.contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
      |>.comp_hasDerivAt s (boxPoint_hasDerivAt_s t s)
  have hhor := interval_point_square_bound ht
    (hfc.comp (by unfold boxPoint; fun_prop) (fun t ht' => boxPoint_mem ht' hy))
    (hfxc.comp (by unfold boxPoint; fun_prop) (fun t ht' => boxPoint_mem ht' hy)) hdt hx
  have hvf := rectangle_vertical_trace_square_bound ht.le hs hfc hfyc hds hy
  have hvx := rectangle_vertical_trace_square_bound ht.le hs hfxc hfyxc hdxs hy
  have hL : 0 ≤ 1 + 1 / (tr - tl) :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (sub_nonneg.mpr ht.le))
  have hscale := mul_le_mul_of_nonneg_left hvf hL
  simp only [Function.comp_def] at hhor
  nlinarith only [hscale, hvx, hhor]

end SmoothLocal.Sobolev

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Energy_RegionSobolev
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem rectangleIntegral_eq_coordinate_area
    {tl tr sb st : ℝ} {F : Coord → ℝ} (ht : tl ≤ tr) (hs : sb ≤ st)
    (hF : ContinuousOn F (closedRectangle tl tr sb st)) :
    rectangleIntegral tl tr sb st F = ∫ p in halfOpenCoordinateRectangle tl tr sb st, F p := by
  rw [rectangleIntegral_eq_area ht hs hF]
  have h := (volume_preserving_finTwoArrow ℝ).setIntegral_preimage_emb
    (MeasurableEquiv.finTwoArrow (α := ℝ)).measurableEmbedding
    (fun p : ℝ × ℝ => F (boxPoint p.1 p.2)) (Ioc tl tr ×ˢ Ioc sb st)
  change (∫ p in halfOpenCoordinateRectangle tl tr sb st, F (boxPoint (p 0) (p 1))) =
    ∫ p in Ioc tl tr ×ˢ Ioc sb st, F (boxPoint p.1 p.2) at h
  simpa only [boxPoint_eta] using h.symm

theorem rectangle_square_integral_le_region
    {tl tr sb st : ℝ} {f : Coord → ℝ} {V : Set Coord}
    (ht : tl ≤ tr) (hs : sb ≤ st)
    (hf : ContinuousOn f (closedRectangle tl tr sb st))
    (hsub : closedRectangle tl tr sb st ⊆ V) (hLp : MemLp f 2 (volume.restrict V)) :
    rectangleIntegral tl tr sb st (fun p => f p ^ 2) ≤ ∫ p in V, f p ^ 2 := by
  have hfsq : ContinuousOn (fun p => f p^2) (closedRectangle tl tr sb st) := hf.pow 2
  rw [rectangleIntegral_eq_coordinate_area ht hs hfsq]
  have hhalf : halfOpenCoordinateRectangle tl tr sb st ⊆ V := by
    intro p hp
    exact hsub ⟨⟨hp.1.1.le, hp.1.2⟩, ⟨hp.2.1.le, hp.2.2⟩⟩
  exact setIntegral_mono_set hLp.integrable_sq
    (Filter.Eventually.of_forall (fun p => sq_nonneg (f p))) hhalf.eventuallyLE

def regionSobolevEnergy (r : ℝ) (V : Set Coord) (f : Coord → ℝ) : ℝ :=
  squareSobolevWeight r * squareSobolevWeight r * (∫ p in V, f p ^ 2) +
  squareSobolevWeight r * (∫ p in V, coordPartial 0 f p ^ 2) +
  squareSobolevWeight r * (∫ p in V, coordPartial 1 f p ^ 2) +
  ∫ p in V, coordPartial 1 (coordPartial 0 f) p ^ 2

theorem point_square_bound_on_region
    {f : Coord → ℝ} {U V : Set Coord} {p : Coord} {r : ℝ} (hr : 0 < r)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hVU : V ⊆ U)
    (hsquare : closedRectangle (p 0 - r) (p 0 + r) (p 1 - r) (p 1 + r) ⊆ V)
    (h0 : MemLp f 2 (volume.restrict V))
    (hx : MemLp (coordPartial 0 f) 2 (volume.restrict V))
    (hy : MemLp (coordPartial 1 f) 2 (volume.restrict V))
    (hxy : MemLp (coordPartial 1 (coordPartial 0 f)) 2 (volume.restrict V)) :
    f p ^ 2 ≤ regionSobolevEnergy r V f := by
  have ht : p 0 - r < p 0 + r := by linarith
  have hs : p 1 - r < p 1 + r := by linarith
  have hbox := hsquare.trans hVU
  have hfx := partial_contDiffOn hf hU 0
  have hfy := partial_contDiffOn hf hU 1
  have hfyx := partial_contDiffOn hfx hU 1
  have hSob := rectangle_point_square_bound ht hs hU hf hbox
    (x := p 0) (y := p 1) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have hw : 0 ≤ squareSobolevWeight r := by
    unfold squareSobolevWeight
    exact add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  have hE0 := rectangle_square_integral_le_region ht.le hs.le (hf.continuousOn.mono hbox) hsquare h0
  have hEx := rectangle_square_integral_le_region ht.le hs.le (hfx.continuousOn.mono hbox) hsquare hx
  have hEy := rectangle_square_integral_le_region ht.le hs.le (hfy.continuousOn.mono hbox) hsquare hy
  have hExy := rectangle_square_integral_le_region ht.le hs.le (hfyx.continuousOn.mono hbox) hsquare hxy
  have hwidth0 : (p 0 + r) - (p 0 - r) = 2 * r := by ring
  have hwidth1 : (p 1 + r) - (p 1 - r) = 2 * r := by ring
  rw [boxPoint_eta, hwidth0, hwidth1] at hSob
  change f p ^ 2 ≤ squareSobolevWeight r * squareSobolevWeight r * _ +
    squareSobolevWeight r * _ + squareSobolevWeight r * _ + _ at hSob
  exact hSob.trans (add_le_add (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hE0 (mul_nonneg hw hw))
      (mul_le_mul_of_nonneg_left hEx hw))
    (mul_le_mul_of_nonneg_left hEy hw)) hExy)

theorem point_abs_bound_on_region
    {f : Coord → ℝ} {U V : Set Coord} {p : Coord} {r : ℝ} (hr : 0 < r)
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hVU : V ⊆ U)
    (hsquare : closedRectangle (p 0 - r) (p 0 + r) (p 1 - r) (p 1 + r) ⊆ V)
    (h0 : MemLp f 2 (volume.restrict V))
    (hx : MemLp (coordPartial 0 f) 2 (volume.restrict V))
    (hy : MemLp (coordPartial 1 f) 2 (volume.restrict V))
    (hxy : MemLp (coordPartial 1 (coordPartial 0 f)) 2 (volume.restrict V)) :
    |f p| ≤ Real.sqrt (regionSobolevEnergy r V f) := by
  have h := point_square_bound_on_region hr hU hf hVU hsquare h0 hx hy hxy
  have he : 0 ≤ regionSobolevEnergy r V f := (sq_nonneg _).trans h
  nlinarith [Real.sq_sqrt he, Real.sqrt_nonneg (regionSobolevEnergy r V f), sq_abs (f p), abs_nonneg (f p)]

end SmoothLocal.Sobolev

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_MixedCoordinateCalculus
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

theorem orderedPartial_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Coord → E} {U : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (ds : List (Fin 2)) :
    ContDiffOn ℝ ∞ (iteratedCoordPartial ds f) U := by
  induction ds with
  | nil => exact hf
  | cons i ds ih => exact normed_coordPartial_contDiffOn ih hU i

end SmoothLocal.HighEquation

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Flows_FlowSobolev
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

variable {q f : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
variable (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
variable (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
variable (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  Y s t ∈ Icc (-3 : ℝ) 3)
variable (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
variable (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
  HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)

include hSU hrange

include hq hU hY hstart hode

theorem actual_flow_interior_sobolev
    {M tl tr sb st dt ds : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ) / 100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds) (hf : ContDiffOn ℝ ∞ f U)
    (h0 : MemLp f 2 (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    (hx : MemLp (coordPartial 0 f) 2 (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    (hy : MemLp (coordPartial 1 f) 2 (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    (hxy : MemLp (coordPartial 1 (coordPartial 0 f)) 2
      (volume.restrict (capChart Y '' closedRectangle tl tr sb st)))
    {p : Coord}
    (hp : p ∈ capChart Y '' closedRectangle (tl + dt) (tr - dt) (sb + ds) (st - ds)) :
    |f p| ≤ Real.sqrt (regionSobolevEnergy (flowInteriorRadius M dt ds)
      (capChart Y '' closedRectangle tl tr sb st) f) := by
  obtain ⟨hr, hmargin⟩ := actual_flow_uniform_image_margin hq hU hSU hY hrange hstart hode
    hM hq0 hq1 htl htr hsb hst hdt hds
  have hsquare := (hmargin p hp).trans (Set.image_mono
    (openCoordinateRectangle_subset_closed tl tr sb st))
  exact point_abs_bound_on_region hr hU hf
    (actual_closed_flow_rectangle_subset_domain hSU hrange htl htr hsb hst)
    hsquare h0 hx hy hxy

end SmoothLocal.Flow

namespace SmoothLocal.Sobolev
open SmoothLocal.Geometry

theorem regionSobolevEnergy_nonneg {r : ℝ} (hr : 0 < r) (V : Set Coord) (f : Coord → ℝ) :
    0 ≤ regionSobolevEnergy r V f := by
  have hw : 0 ≤ squareSobolevWeight r :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  exact add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_nonneg hw hw) (integral_nonneg (fun p => sq_nonneg (f p))))
    (mul_nonneg hw (integral_nonneg (fun p => sq_nonneg (coordPartial 0 f p)))))
    (mul_nonneg hw (integral_nonneg (fun p => sq_nonneg (coordPartial 1 f p)))))
    (integral_nonneg (fun p => sq_nonneg (coordPartial 1 (coordPartial 0 f) p)))

theorem regionSobolevEnergy_le_common_bound
    {r B : ℝ} {V : Set Coord} {f : Coord → ℝ} (hr : 0 < r)
    (h0 : (∫ p in V, f p ^ 2) ≤ B ^ 2)
    (hx : (∫ p in V, coordPartial 0 f p ^ 2) ≤ B ^ 2)
    (hy : (∫ p in V, coordPartial 1 f p ^ 2) ≤ B ^ 2)
    (hxy : (∫ p in V, coordPartial 1 (coordPartial 0 f) p ^ 2) ≤ B ^ 2) :
    regionSobolevEnergy r V f ≤ ((squareSobolevWeight r + 1) * B)^2 := by
  have hw : 0 ≤ squareSobolevWeight r :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  calc
    regionSobolevEnergy r V f ≤
        squareSobolevWeight r * squareSobolevWeight r * B^2 +
        squareSobolevWeight r * B^2 + squareSobolevWeight r * B^2 + B^2 :=
      add_le_add (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h0 (mul_nonneg hw hw))
        (mul_le_mul_of_nonneg_left hx hw)) (mul_le_mul_of_nonneg_left hy hw)) hxy
    _ = _ := by ring

theorem abs_bound_of_regionSobolevEnergy
    {r B : ℝ} {V : Set Coord} {f : Coord → ℝ} {p : Coord}
    (hr : 0 < r) (hB : 0 ≤ B) (hp : |f p| ≤ Real.sqrt (regionSobolevEnergy r V f))
    (h0 : (∫ q in V, f q ^ 2) ≤ B ^ 2)
    (hx : (∫ q in V, coordPartial 0 f q ^ 2) ≤ B ^ 2)
    (hy : (∫ q in V, coordPartial 1 f q ^ 2) ≤ B ^ 2)
    (hxy : (∫ q in V, coordPartial 1 (coordPartial 0 f) q ^ 2) ≤ B ^ 2) :
    |f p| ≤ (squareSobolevWeight r + 1) * B := by
  have hE := regionSobolevEnergy_nonneg hr V f
  have henergy := regionSobolevEnergy_le_common_bound hr h0 hx hy hxy
  have hw : 0 ≤ squareSobolevWeight r :=
    add_nonneg zero_le_one (div_nonneg zero_le_one (mul_nonneg (by norm_num) hr.le))
  have hbound : 0 ≤ (squareSobolevWeight r + 1) * B := mul_nonneg (by linarith) hB
  have hroot : Real.sqrt (regionSobolevEnergy r V f) ≤ (squareSobolevWeight r + 1) * B := by
    nlinarith [Real.sq_sqrt hE, Real.sqrt_nonneg (regionSobolevEnergy r V f)]
  exact hp.trans hroot

end SmoothLocal.Sobolev

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapL2Basics
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Analytic

def CoordinateL2Bound (z : Coord → ℝ) (V : Set Coord) (N : ℕ) (H : ℝ≥0) : Prop :=
  ∀ ds : List (Fin 2), ds.length ≤ N →
    eLpNorm' (iteratedCoordPartial ds z) (2 : ℝ) (volume.restrict V) ≤ (H : ℝ≥0∞)

theorem CoordinateL2Bound.eLpNorm_le {z : Coord → ℝ} {V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (hbound : CoordinateL2Bound z V N H) (word : List (Fin 2)) (hword : word.length ≤ N)
    (hmeas : AEStronglyMeasurable (iteratedCoordPartial word z) (volume.restrict V)) :
    eLpNorm (iteratedCoordPartial word z) 2 (volume.restrict V) ≤ (H : ℝ≥0∞) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ENNReal.toReal_ofNat]
  exact hbound word hword

theorem CoordinateL2Bound.memLp {z : Coord → ℝ} {U V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (ds : List (Fin 2)) (hds : ds.length ≤ N) :
    MemLp (iteratedCoordPartial ds z) 2 (volume.restrict V) := by
  have hmeas := ((orderedPartial_contDiffOn hz hU ds).continuousOn.mono
    hVU).aestronglyMeasurable (μ := volume) hV
  exact ⟨hmeas, (h.eLpNorm_le ds hds hmeas).trans_lt (by finiteness)⟩

theorem CoordinateL2Bound.integral_sq {z : Coord → ℝ} {U V : Set Coord} {N : ℕ} {H : ℝ≥0}
    (h : CoordinateL2Bound z V N H) (hz : ContDiffOn ℝ ∞ z U) (hU : IsOpen U)
    (hV : MeasurableSet V) (hVU : V ⊆ U) (ds : List (Fin 2)) (hds : ds.length ≤ N) :
    (∫ p in V, iteratedCoordPartial ds z p ^ 2) ≤ (H : ℝ)^2 := by
  have hmem := h.memLp hz hU hV hVU ds hds
  exact integral_sq_le_of_eLpNorm_two_le hmem (h.eLpNorm_le ds hds hmem.aestronglyMeasurable)

end SmoothLocal.HighEquation

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Sobolev
open SmoothLocal.HighEquation

theorem coordinateL2Bound_to_nested_flow_coordinateBound
    {q z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {M tl tr sb st dt ds : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (htl : -2 < tl) (htr : tr < 2) (hsb : -2 < sb) (hst : st < 2)
    (hdt : 0 < dt) (hds : 0 < ds) (hz : ContDiffOn ℝ ∞ z U)
    {n : ℕ} {H : ℝ≥0}
    (hL : CoordinateL2Bound z (capChart Y '' closedRectangle tl tr sb st) (n + 2) H) :
    CoordinateBound z
      (capChart Y '' closedRectangle (tl+dt) (tr-dt) (sb+ds) (st-ds)) n
      ((squareSobolevWeight (flowInteriorRadius M dt ds)+1)*(H : ℝ)) := by
  let V := capChart Y '' closedRectangle tl tr sb st
  have hVU : V ⊆ U := actual_closed_flow_rectangle_subset_domain hSU hrange htl htr hsb hst
  have hYs := cap_flow_joint_contDiffOn hq hU hSU hY hrange hstart hode
  have hcompact : IsCompact V := (capRectangle_isCompact tl tr sb st).image_of_continuousOn
    ((capChart_contDiffOn hYs).continuousOn.mono
      (closedRectangle_subset_capChartDomain htl htr hsb hst))
  have hV : MeasurableSet V := hcompact.isClosed.measurableSet
  intro word hword p hp
  have h0 := hL.memLp hz hU hV hVU word (by omega)
  have hx := hL.memLp hz hU hV hVU (0 :: word) (by simp only [List.length_cons]; omega)
  have hy := hL.memLp hz hU hV hVU (1 :: word) (by simp only [List.length_cons]; omega)
  have hxy := hL.memLp hz hU hV hVU (1 :: 0 :: word) (by simp only [List.length_cons]; omega)
  have hpoint := actual_flow_interior_sobolev hq hU hSU hY hrange hstart hode hM hq0 hq1
    htl htr hsb hst hdt hds (orderedPartial_contDiffOn hz hU word) h0 hx hy hxy hp
  exact abs_bound_of_regionSobolevEnergy (flowInteriorRadius_pos M hdt hds) H.2 hpoint
    (hL.integral_sq hz hU hV hVU word (by omega))
    (hL.integral_sq hz hU hV hVU (0 :: word) (by simp only [List.length_cons]; omega))
    (hL.integral_sq hz hU hV hVU (1 :: word) (by simp only [List.length_cons]; omega))
    (hL.integral_sq hz hU hV hVU (1 :: 0 :: word) (by simp only [List.length_cons]; omega))

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

namespace LowerCapRectangle

variable {bStar : ℝ}

theorem region_subset_energyOuter (r : LowerCapRectangle bStar) : r.region ⊆ r.energyOuter.region := by
  obtain ⟨_,_,_,_,_,_,_,hB0,hB1,hL,hR⟩ := capOuterRectangle_edges r.left_gt r.right_lt r.bottom_gt
  intro p hp
  exact ⟨⟨by change capOuterLeft r.left ≤ p 0; linarith [hp.1.1],
    by change p 0 ≤ capOuterRight r.right; linarith [hp.1.2]⟩,
    ⟨by change capOuterBottom r.bottom ≤ p 1; linarith [hp.2.1],
      by change p 1 ≤ (r.top+bStar)/2; linarith [hp.2.2,r.top_lt]⟩⟩

theorem region_subset_expand (r : LowerCapRectangle bStar) : r.region ⊆ r.expand.region := by
  intro p hp
  exact ⟨⟨by change r.left-r.margin ≤ p 0; linarith [hp.1.1,r.margin_pos],
    by change p 0 ≤ r.right+r.margin; linarith [hp.1.2,r.margin_pos]⟩,
    ⟨by change r.bottom-r.margin ≤ p 1; linarith [hp.2.1,r.margin_pos],
      by change p 1 ≤ r.top+r.margin; linarith [hp.2.2,r.margin_pos]⟩⟩

theorem image_subset_energyOuter (r : LowerCapRectangle bStar) (Y : ℝ → ℝ → ℝ) :
    r.image Y ⊆ r.energyOuter.image Y := Set.image_mono r.region_subset_energyOuter

theorem image_subset_expand (r : LowerCapRectangle bStar) (Y : ℝ → ℝ → ℝ) :
    r.image Y ⊆ r.expand.image Y := Set.image_mono r.region_subset_expand

end LowerCapRectangle

variable {bStar : ℝ}

theorem coordinateL2Bound_to_expanded_cap_coordinateBound
    {q z : Coord → ℝ} {U : Set Coord} {Y : ℝ → ℝ → ℝ}
    (hq : ContDiffOn ℝ ∞ q U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hY : ContinuousOn (uncurry Y) (Icc (-2 : ℝ) 2 ×ˢ Icc (-2 : ℝ) 2))
    (hrange : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2, Y s t ∈ Icc (-3 : ℝ) 3)
    (hstart : ∀ s ∈ Icc (-2 : ℝ) 2, Y s 0 = s)
    (hode : ∀ s ∈ Icc (-2 : ℝ) 2, ∀ t ∈ Icc (-2 : ℝ) 2,
      HasDerivWithinAt (Y s) (-q (coordinatePoint t (Y s t))) (Icc (-2 : ℝ) 2) t)
    {M : ℝ} (hM : 0 ≤ M)
    (hq0 : ∀ p ∈ modelSquare, |q p| ≤ (1 : ℝ)/100)
    (hq1 : ∀ p ∈ modelSquare, |coordPartial 1 q p| ≤ M)
    (hz : ContDiffOn ℝ ∞ z U) (r : LowerCapRectangle bStar) {n : ℕ} {H : ℝ≥0}
    (hL : SmoothLocal.HighEquation.CoordinateL2Bound z (r.expand.image Y) (n+2) H) :
    CoordinateBound z (r.image Y) n
      ((SmoothLocal.Sobolev.squareSobolevWeight (flowInteriorRadius M r.margin r.margin)+1)*(H : ℝ)) := by
  have h := coordinateL2Bound_to_nested_flow_coordinateBound hq hU hSU hY hrange hstart hode
    hM hq0 hq1 r.expand.left_gt r.expand.right_lt r.expand.bottom_gt
    (by linarith [r.expand.top_lt,r.expand.ceiling_le]) r.margin_pos r.margin_pos hz hL
  simpa only [LowerCapRectangle.expand_shrink_region, LowerCapRectangle.image] using h

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_CapInductionData
attribute [-simp] _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_one _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_twice _root_.OAI.SmoothLocal.Flow.Reflection.reflectPoint_zero _root_.OAI.SmoothLocal.Geometry.affineCoordinates_zero _root_.OAI.SmoothLocal.Geometry.coordPartial_const _root_.OAI.SmoothLocal.Geometry.coordinateSwap_apply _root_.OAI.SmoothLocal.Geometry.coordinateSwap_involutive _root_.OAI.SmoothLocal.Geometry.matrixContinuousLinear_apply _root_.OAI.SmoothLocal.Geometry.openDomainExtend_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_apply _root_.OAI.SmoothLocal.Geometry.swappedMetric_det _root_.OAI.SmoothLocal.Geometry.warpedMetric_00 _root_.OAI.SmoothLocal.Geometry.warpedMetric_01 _root_.OAI.SmoothLocal.Geometry.warpedMetric_10 _root_.OAI.SmoothLocal.Geometry.warpedMetric_11 _root_.OAI.SmoothLocal.Geometry.warpedMetric_det _root_.OAI.SmoothLocal.HighEquation.stateGradient_qToPState _root_.OAI.SmoothLocal.HighEquation.statePoint_qToPState
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

theorem CapInductionFlow.pointwise_from_larger_L2
    {g : MetricField} {U W : Set Coord} {G Z d c e0 kappa : ℝ} {z : Coord → ℝ} {Y : ℝ → ℝ → ℝ}
    (hh : CapInductionHeight g U Z c e0 z) (hf : CapInductionFlow g U G Z d c e0 kappa z Y W)
    (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    (r : LowerCapRectangle bStar) {n : ℕ} {H : ℝ≥0}
    (hL : CoordinateL2Bound z (r.expand.image Y) (n+2) H) :
    CoordinateBound z (r.image Y) n
      ((squareSobolevWeight (flowInteriorRadius (heightQuotientJetBound G Z d c) r.margin r.margin)+1)*(H : ℝ)) := by
  apply coordinateL2Bound_to_expanded_cap_coordinateBound hf.quotientSmooth hf.domainOpen hf.squareSubset
    hf.continuous hf.range hf.start hf.ode (heightQuotientJetBound_nonneg hG hZ hd hc)
    hh.quotient (fun p hp => hf.quotientBound [1] (by norm_num) p hp)
    (hh.smooth.mono hf.domainSubset) r hL

def originalC8L2Budget (Z : ℝ) : ℝ≥0 :=
  (‖Z‖ₑ * (volume modelSquare) ^ (1/(2 : ℝ))).toNNReal

theorem originalC8L2Budget_coe (Z : ℝ) :
    (originalC8L2Budget Z : ℝ≥0∞) = ‖Z‖ₑ * (volume modelSquare) ^ (1/(2 : ℝ)) := by
  apply ENNReal.coe_toNNReal
  exact (ENNReal.mul_lt_top (by finiteness)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) modelSquare_isCompact.measure_lt_top.ne)).ne

theorem CapInductionHeight.original_L2
    {g : MetricField} {U : Set Coord} {Z c e0 : ℝ} {z : Coord → ℝ}
    (hh : CapInductionHeight g U Z c e0 z) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hZ : 0 ≤ Z) {V : Set Coord} (hV : MeasurableSet V) (hVS : V ⊆ modelSquare) :
    CoordinateL2Bound z V 8 (originalC8L2Budget Z) := by
  have hC := coordinateBound_of_frechet_bounds hh.smooth hU hSU hh.lowJet
  intro ds hds
  rw [originalC8L2Budget_coe]
  exact (bounded_real_eLpNorm_two hV hZ (fun p hp => by
    rw [Real.norm_eq_abs]
    exact hC ds hds p (hVS hp))).trans
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (z := 1/(2 : ℝ)) (measure_mono hVS) (by norm_num)))

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_UpperCapWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

namespace UpperCapRectangle
variable {floor : ℝ}

def region (r : UpperCapRectangle floor) : Set Coord :=
  closedRectangle r.left r.right r.bottom r.top

def image (r : UpperCapRectangle floor) (Y : ℝ → ℝ → ℝ) : Set Coord :=
  capChart Y '' r.region

def lower (r : UpperCapRectangle floor) : LowerCapRectangle (-floor) where
  left := r.left
  right := r.right
  bottom := -r.top
  top := -r.bottom
  left_gt := r.left_gt
  right_lt := r.right_lt
  bottom_gt := neg_lt_neg r.top_lt
  horizontal := r.horizontal
  vertical := neg_le_neg r.vertical
  top_lt := neg_lt_neg r.bottom_gt
  ceiling_le := neg_nonpos.mpr r.floor_nonneg

theorem region_subset_domain (r : UpperCapRectangle floor) : r.region ⊆ capChartDomain :=
  closedRectangle_subset_capChartDomain r.left_gt r.right_lt
    (by linarith [r.bottom_gt,r.floor_nonneg]) r.top_lt

theorem image_properties (r : UpperCapRectangle floor) {Y : ℝ → ℝ → ℝ}
    (hchart : ContDiffOn ℝ ∞ (capChart Y) capChartDomain)
    (hdisp : ∀ p ∈ capChartDomain, |capFlowHeight Y p-p 1| ≤ (1 : ℝ)/50) :
    IsCompact (r.image Y) ∧ MeasurableSet (r.image Y) ∧ r.image Y ⊆ modelSquare := by
  have hcompact : IsCompact (r.image Y) :=
    (capRectangle_isCompact r.left r.right r.bottom r.top).image_of_continuousOn
      (hchart.continuousOn.mono r.region_subset_domain)
  refine ⟨hcompact,hcompact.measurableSet,?_⟩
  rintro p ⟨q,hq,rfl⟩
  exact modelOpenSquare_subset
    (capChart_mem_modelOpenSquare (r.region_subset_domain hq) (hdisp q (r.region_subset_domain hq)))

end UpperCapRectangle
end SmoothLocal.Flow.Reflection

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_VaryingCapInduction
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

abbrev CapMetricJetBudget (bStar : ℝ) := ℕ → LowerCapRectangle bStar → ℝ

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_UpperCapMetricJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

def reflectedUpperRectangle {floor : ℝ} (r : LowerCapRectangle (-floor)) :
    UpperCapRectangle floor where
  left := r.left
  right := r.right
  bottom := -r.top
  top := -r.bottom
  left_gt := r.left_gt
  right_lt := r.right_lt
  top_lt := by simpa only [neg_neg] using neg_lt_neg r.bottom_gt
  horizontal := r.horizontal
  vertical := neg_le_neg r.vertical
  bottom_gt := by simpa only [neg_neg] using neg_lt_neg r.top_lt
  floor_nonneg := neg_nonpos.mp r.ceiling_le

end SmoothLocal.Flow.Reflection

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_FiniteCapInduction
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

def lowerCapMetricRequests {bStar : ℝ} : ℕ → LowerCapRectangle bStar →
    List (ℕ × LowerCapRectangle bStar)
  | 0, _ => []
  | k+1, r => (k+8,r.energyOuter)::(k+7,r)::lowerCapMetricRequests k r.energyOuter.expand

def FiniteCapMetricJets {bStar : ℝ} (g : MetricField) (Y : ℝ → ℝ → ℝ)
    (J : CapMetricJetBudget bStar) (L : List (ℕ × LowerCapRectangle bStar)) : Prop :=
  ∀ b ∈ L, ∀ (i j : Fin 2) (n : ℕ), n ≤ b.1+2 →
    ∀ p ∈ b.2.image Y, ‖iteratedFDeriv ℝ n (fun q => g q i j) p‖ ≤ J b.1 b.2

theorem lowerCapMetricRequests_order_le {bStar : ℝ} (k : ℕ)
    (r : LowerCapRectangle bStar) (b : ℕ × LowerCapRectangle bStar)
    (hb : b ∈ lowerCapMetricRequests k r) : b.1 ≤ k+7 := by
  induction k generalizing r with
  | zero => simp [lowerCapMetricRequests] at hb
  | succ k ih =>
    simp only [lowerCapMetricRequests,List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · omega
    · omega
    · have h := ih r.energyOuter.expand hb
      omega

theorem lowerCapMetricRequests_full_order_le {bStar : ℝ} (k : ℕ)
    (r : LowerCapRectangle bStar) (b : ℕ × LowerCapRectangle bStar)
    (hb : b ∈ lowerCapMetricRequests k r) {n : ℕ} (hn : n ≤ b.1+2) : n ≤ k+9 := by
  have h := lowerCapMetricRequests_order_le k r b hb
  omega

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

def lowerCapPointwiseRequests {bStar : ℝ} (n : ℕ) (r : LowerCapRectangle bStar) :
    List (ℕ × LowerCapRectangle bStar) := lowerCapMetricRequests (n-6) r.expand

theorem lowerCapPointwiseRequests_full_order_le {bStar : ℝ} (n : ℕ)
    (r : LowerCapRectangle bStar) (b : ℕ × LowerCapRectangle bStar)
    (hb : b ∈ lowerCapPointwiseRequests n r) {k : ℕ} (hk : k ≤ b.1+2) :
    k ≤ max 8 (n+3) := by
  by_cases hn : n ≤ 6
  · have hn0 : n-6=0 := Nat.sub_eq_zero_of_le hn
    simp [lowerCapPointwiseRequests,hn0,lowerCapMetricRequests] at hb
  · have h := lowerCapMetricRequests_full_order_le (n-6) r.expand b hb hk
    omega

end SmoothLocal.Flow

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Calculus_FiniteUpperMetricJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation

def upperCapPointwiseRequests {floor : ℝ} (n : ℕ) (r : UpperCapRectangle floor) :
    List (ℕ × UpperCapRectangle floor) :=
  (lowerCapPointwiseRequests n r.lower).map (fun b => (b.1,reflectedUpperRectangle b.2))

def FiniteUpperCapMetricJets {floor : ℝ} (g : MetricField) (Y : ℝ → ℝ → ℝ)
    (J : UpperCapMetricJetBudget floor) (L : List (ℕ × UpperCapRectangle floor)) : Prop :=
  ∀ b ∈ L, ∀ (i j : Fin 2) (k : ℕ), k ≤ b.1+2 →
    ∀ p ∈ b.2.image Y, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ J b.1 b.2

theorem upperCapPointwiseRequests_full_order_le {floor : ℝ} (n : ℕ)
    (r : UpperCapRectangle floor) (b : ℕ × UpperCapRectangle floor)
    (hb : b ∈ upperCapPointwiseRequests n r) {k : ℕ} (hk : k ≤ b.1+2) :
    k ≤ max 8 (n+3) := by
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
  exact lowerCapPointwiseRequests_full_order_le n r.lower a ha hk

end SmoothLocal.Flow.Reflection

end

end OAI
end

section
-- module Solutions.Q226_II.IsometricImmersion_Caps_VaryingMetricUpperCap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology ENNReal NNReal

namespace SmoothLocal.Flow.Reflection
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.HighEquation
  SmoothLocal.Model

theorem reflected_capInductionHeight {g : MetricField} {z : Coord → ℝ}
    {U : Set Coord} {Z c e0 : ℝ} (hg : SmoothPositiveOn g U) (hU : IsOpen U)
    (hSU : modelSquare ⊆ U) (hh : CapInductionHeight g U Z c e0 z) :
    CapInductionHeight (reflectedMetric g) (reflectPoint ⁻¹' U) Z c e0 (reflectedScalar z) := by
  have hmem {p : Coord} (hp : p ∈ modelSquare) : reflectPoint p ∈ U :=
    hSU ((reflectPoint_mem_modelSquare p).mpr hp)
  refine ⟨reflectedScalar_contDiffOn hh.smooth, reflectedScalar_C8 hh.lowJet, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [reflectedMetric_hessian_entry hg hh.smooth hU (hmem hp)]
    simp only [ite_true, if_true]
    exact hh.denominator _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_energy hh.smooth hU (hmem hp)]
    exact hh.energy _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_quotient hg hh.smooth hU (hmem hp), abs_neg]
    exact hh.quotient _ ((reflectPoint_mem_modelSquare p).mpr hp)
  · intro p hp
    rw [reflectedMetric_hessian_det hg hh.smooth hU (hmem hp),
      reflectedMetric_curvature hg hU (hmem hp), reflectedMetric_energy hh.smooth hU (hmem hp)]
    exact hh.darboux _ ((reflectPoint_mem_modelSquare p).mpr hp)

end SmoothLocal.Flow.Reflection

end

end OAI
end


