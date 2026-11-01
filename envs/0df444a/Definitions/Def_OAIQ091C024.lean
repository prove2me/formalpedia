-- Prove2me | Definitions.Def_OAIQ091C024
-- name    : OAIQ091C024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:21:38.646368+00:00
-- url     : https://prove2.me/theorems/256e9b01-f76b-4b91-83a4-a43a9aae923a
-- title:
--   Definitions bundle OAIQ091C024 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 315 declarations of OpenAI's Lean: 47 definitions, 1 inductive type or structure, 2 instances and 265 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.HeatEulerChartData`, `OAI.PositiveEinsteinFour.Geometry.HeatEulerChartData.bundle`, `OAI.PositiveEinsteinFour.Geometry.HeatEulerChartData.scalar`, `OAI.PositiveEinsteinFour.Geometry.HeatFamilySmoothCoefficients.lastCoefficient`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.eulerAmplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.eulerFirst`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.eulerPolynomial`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.eulerSecondAmplitude`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.eulerSecondWeight`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.eulerTail`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.oneTimeColumn`, `OAI.PositiveEinsteinFour.Geometry.OneFormC0`, `OAI.PositiveEinsteinFour.Geometry.halfSmoothCutoff`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyDrift`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyOneZero`, `OAI.PositiveEinsteinFour.Geometry.heatFamilySignedFirst`, `OAI.PositiveEinsteinFour.Geometry.heatFamilySignedTail`, `OAI.PositiveEinsteinFour.Geometry.heatFamilyZero`, `OAI.PositiveEinsteinFour.Geometry.heatNormalOneGlobalTimeColumn`, `OAI.PositiveEinsteinFour.Geometry.heatNormalOneResidualColumn`, `OAI.PositiveEinsteinFour.Geometry.heatNormalOneTimeColumn`, `OAI.PositiveEinsteinFour.Geometry.heatNormalResidualColumn`, `OAI.PositiveEinsteinFour.Geometry.heatNormalTimeColumn`, `OAI.PositiveEinsteinFour.Geometry.hodgeEulerTracePolynomial`, `OAI.PositiveEinsteinFour.Geometry.hodgeSignatureTracePolynomial`, `OAI.PositiveEinsteinFour.Geometry.oneFormC0BaseNorm`, `OAI.PositiveEinsteinFour.Geometry.oneFormC0ToFrameLp`, `OAI.PositiveEinsteinFour.Geometry.oneFormContinuousSubspace`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseHeatWeight`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseResolventJet`, `OAI.PositiveEinsteinFour.Geometry.scalarChartSourceL2`, `OAI.PositiveEinsteinFour.Geometry.scalarCoercive_meanZeroInner`, `OAI.PositiveEinsteinFour.Geometry.scalarEigenCutoff`, `OAI.PositiveEinsteinFour.Geometry.scalarFiniteLaplacianL2`, `OAI.PositiveEinsteinFour.Geometry.scalarFirstJetDifferential`, `OAI.PositiveEinsteinFour.Geometry.scalarFirstJetDifferentialCLM`, `OAI.PositiveEinsteinFour.Geometry.scalarFirstJetRangeEquiv`, `OAI.PositiveEinsteinFour.Geometry.scalarH1Differential`, `OAI.PositiveEinsteinFour.Geometry.scalarLocalL2Gradient`, `OAI.PositiveEinsteinFour.Geometry.scalarLocalL2PartialProduct` and 8 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean), [`EinsteinFour_WeylEstimates07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C019`, `OAIQ091C040` and `OAIQ091C041` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C027`, `OAIQ091C028`, `OAIQ091C029`, `OAIQ091C045`, `OAIQ091C046`, `OAIQ091C047`, `OAIQ091C050`, `OAIQ091C052`, `OAIQ091C053`, `OAIQ091C055` and `OAIQ091C056`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C019
import Definitions.Def_OAIQ091C040
import Definitions.Def_OAIQ091C041

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The Hilbert completion of actual smooth two-form sections with their
intrinsic L2 pairing. The inclusion of pointwise smooth sections is an
injective linear isometry with dense range. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

/- The L2 topology of the completion differs from the pointwise topology
on the smooth function submodule. -/

theorem smoothTwoFormToL2_injective : Function.Injective (smoothTwoFormToL2 (o := o)) :=
  (smoothTwoFormToL2 (o := o)).injective

theorem smoothTwoFormToL2_inner (u v : SmoothL2TwoForm o) :
    inner ℝ (smoothTwoFormToL2 u) (smoothTwoFormToL2 v) =
      ∫ x, inner ℝ ((u : smoothTwoForms o).val x)
        ((v : smoothTwoForms o).val x) ∂normalizedVolume g := by
  exact UniformSpace.Completion.inner_coe u v

theorem smoothTwoFormToL2_norm_sq (u : SmoothL2TwoForm o) :
    ‖smoothTwoFormToL2 u‖ ^ 2 =
      ∫ x, ‖(u : smoothTwoForms o).val x‖ ^ 2 ∂normalizedVolume g := by
  rw [smoothTwoFormToL2.norm_map, smoothTwoForm_norm_sq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The concrete two-form connection action in a local orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem twoFormLocalNabla_hodge (c : M) (S : Mat4) {a : FourSpace → TwoFormFour}
    {z : FourSpace} (ha : DifferentiableAt ℝ a z) (i : Fin 4) :
    twoFormLocalNabla (g := g) c S (fun w => twoFormHodge (a w)) i z =
      twoFormHodge (twoFormLocalNabla (g := g) c S a i z) := by
  have hd := (twoFormHodge.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp z
    ha.hasFDerivAt).fderiv
  have heval : fderiv ℝ (fun w => twoFormHodge (a w)) z (coordinateVector i) =
      twoFormHodge (fderiv ℝ a z (coordinateVector i)) :=
    congrArg (fun D : FourSpace →L[ℝ] TwoFormFour => D (coordinateVector i)) hd
  unfold twoFormLocalNabla
  rw [heval, twoFormSkewAction_hodge, map_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! In Ric = 3g the local graded traces of the Weitzenböck potential
have vanishing degree-zero/degree-one terms and the required curvature norm
in degree two. No heat-kernel or characteristic-number assertion is made. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem actual_twoFormPotential_square_trace (hRic : RicciThree g) (e : FrameBundle g) :
    (twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
      twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace - 72 =
        frameTensorSquareNorm (twoFormMetricCurvatureTensor g e) := by
  let R := twoFormMetricCurvatureTensor g e
  have hl (i j k l : Fin 4) : R ![i,j,l,k] = -R ![i,j,k,l] := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  have hp (i j k l : Fin 4) : R ![k,l,i,j] = R ![i,j,k,l] := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame) i j k l
  have hn := twoFormCurvatureMatrix_tensorNorm R (twoFormMetricCurvatureTensor_skew g e) hl
  rw [twoFormPotentialMatrix_square_trace, actual_twoFormCurvatureMatrix_trace hRic,
    twoFormCurvatureMatrix_square_trace R hp]
  change 216 - 24 * 6 + 4 * (∑ i, ∑ j, twoFormCurvatureMatrix R i j ^ 2) - 72 = _
  linarith only [hn]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reconstruction of the full covariant derivative in a local frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.localNablaRows_hodge {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target)
    (hp : ∀ w (hw : w ∈ U), chartGramSection g c S hS ⟨w, hUt hw⟩ ∈ o.positive)
    (z : FourSpace) (hzU : z ∈ U) (i : Fin 4) :
    twoFormLocalNablaRows (g := g) c S
      (twoFormChartValue o (fun x => twoFormHodge (u x)) c S hS) z i =
        twoFormHodge (twoFormLocalNablaRows (g := g) c S (twoFormChartValue o u c S hS) z i) := by
  have he : twoFormChartValue o (fun x => twoFormHodge (u x)) c S hS =ᶠ[𝓝 z]
      fun w => twoFormHodge (twoFormChartValue o u c S hS w) := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    simp only [twoFormChartValue, dite_eq_left (hUt hw)]
    exact twoFormFrameValue_hodge o u _ (hp w hw)
  have ha : DifferentiableAt ℝ (twoFormChartValue o u c S hS) z :=
    ((hu c S hS U hU hUt hp).contDiffAt (hU.mem_nhds hzU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  unfold twoFormLocalNablaRows
  simp_rw [twoFormLocalNabla_congr c S he, twoFormLocalNabla_hodge c S ha,
    map_sum, map_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The connection-curvature contributions to the Euler and signature
local trace polynomials, with the actual covariant-slot convention. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

def twoFormConnectionCurvatureMatrix (R : CovariantCoordinates 4) (i j : Fin 4) : TwoFormMatrix :=
  -twoFormInfinitesimalMatrix (twoFormCurvatureRow R i j)

theorem connectionCurvature_euler_trace (R : CovariantCoordinates 4)
    (hl : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l]) (i j : Fin 4) :
    (twoFormConnectionCurvatureMatrix R i j * twoFormConnectionCurvatureMatrix R i j).trace -
      2 * (oneFormConnectionCurvatureMatrix R i j * oneFormConnectionCurvatureMatrix R i j).trace = 0 := by
  have hm : oneFormConnectionCurvatureMatrix R i j = -twoFormMatrix (twoFormCurvatureRow R i j) := by
    rw [twoFormMatrix_curvatureRow R hl]
    rfl
  rw [hm, twoFormConnectionCurvatureMatrix]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  exact twoFormInfinitesimalMatrix_euler_trace _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The quadratic local trace polynomials for the normalized Hodge and
signature operators equal the actual characteristic curvature densities.
 -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

def hodgeEulerTracePolynomial (R : CovariantCoordinates 4) : ℝ :=
  (((twoFormPotentialMatrix R * twoFormPotentialMatrix R).trace - 72) / 2 +
    (∑ i, ∑ j,
      ((twoFormConnectionCurvatureMatrix R i j * twoFormConnectionCurvatureMatrix R i j).trace -
      2 * (oneFormConnectionCurvatureMatrix R i j * oneFormConnectionCurvatureMatrix R i j).trace)) / 12) /
    (16 * Real.pi ^ 2)

def hodgeSignatureTracePolynomial (R : CovariantCoordinates 4) : ℝ :=
  ((twoFormHodgeMatrix * twoFormPotentialMatrix R * twoFormPotentialMatrix R).trace / 2 +
    (∑ i, ∑ j, (twoFormHodgeMatrix * twoFormConnectionCurvatureMatrix R i j *
      twoFormConnectionCurvatureMatrix R i j).trace) / 12) / (16 * Real.pi ^ 2)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem actual_hodgeEulerTracePolynomial (hRic : RicciThree g) (e : FrameBundle g) :
    hodgeEulerTracePolynomial (twoFormMetricCurvatureTensor g e) =
      curvatureEulerDensity (twoFormMetricCurvatureTensor g e) := by
  let R := twoFormMetricCurvatureTensor g e
  have hl (i j k l : Fin 4) : R ![i,j,l,k] = -R ![i,j,k,l] := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  have hr (j k : Fin 4) : (∑ i : Fin 4, R ![i,j,k,i]) = if j = k then 3 else 0 := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_ricciThree e.frame hRic j k
  change hodgeEulerTracePolynomial R = curvatureEulerDensity R
  rw [hodgeEulerTracePolynomial, actual_twoFormPotential_square_trace hRic e]
  simp only [connectionCurvature_euler_trace R hl, Finset.sum_const_zero, zero_div, add_zero]
  rw [curvatureEulerDensity]
  simp only [hr, Fin.sum_univ_four]
  norm_num
  ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instCompleteSpace_h1 _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! A genuine local normal-coordinate chart for the constructed radial
exponential, obtained from its actual derivative at zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

variable [T3Space M]

/-- The actual exponential agrees on a neighborhood of zero with a local
homeomorphism onto a neighborhood of its base point. -/
theorem frameExponential_localChart (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ C : OpenPartialHomeomorph FourSpace M,
      0 ∈ C.source ∧ EqOn C (frameExponential g o e) C.source := by
  let L := e.frame.map.toContinuousLinearMap
  have hL : IsUnit L := frameMap_isUnit g e
  let E : FourSpace ≃L[ℝ] FourSpace := ContinuousLinearEquiv.ofUnit hL.unit
  have hE : (E : FourSpace →L[ℝ] FourSpace) = L := hL.unit_spec
  have hf : HasStrictFDerivAt
      (fun v : FourSpace => chartAt FourSpace e.base (frameExponential g o e v))
      (E : FourSpace →L[ℝ] FourSpace) 0 := by
    rw [hE]
    have h := frameExponential_chart_strictDerivative_zero g o e.base e
      (mem_chart_source FourSpace e.base)
    simpa only [chartForwardOperator_center, ContinuousLinearMap.id_comp] using h
  let C := hf.toOpenPartialHomeomorph _
  let U := (frameExponential g o e) ⁻¹' (chartAt FourSpace e.base).source
  have hU : IsOpen U := (chartAt FourSpace e.base).open_source.preimage
    (frameExponential_continuous g o e)
  let D := (C.trans (chartAt FourSpace e.base).symm).restrOpen U hU
  have hzero : (0 : FourSpace) ∈ U := by
    change frameExponential g o e 0 ∈ (chartAt FourSpace e.base).source
    rw [frameExponential_zero]
    exact mem_chart_source FourSpace e.base
  refine ⟨D, ?_, ?_⟩
  · change 0 ∈ (C.trans (chartAt FourSpace e.base).symm).source ∩ U
    refine ⟨⟨hf.mem_toOpenPartialHomeomorph_source, ?_⟩, hzero⟩
    change chartAt FourSpace e.base (frameExponential g o e 0) ∈
      (chartAt FourSpace e.base).target
    exact (chartAt FourSpace e.base).map_source hzero
  · intro v hv
    have hvU : v ∈ U := hv.2
    change (chartAt FourSpace e.base).symm
      (chartAt FourSpace e.base (frameExponential g o e v)) = frameExponential g o e v
    exact (chartAt FourSpace e.base).left_inv hvU

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic L2 pairing of actual smooth one-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.oneFormPairingCompactFrames
theorem smoothOneFormL2Pairing_sub (u v w : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (u - v) w =
      smoothOneFormL2Pairing (o := o) u w - smoothOneFormL2Pairing (o := o) v w := by
  rw [sub_eq_add_neg, smoothOneFormL2Pairing_add, ← neg_one_smul ℝ v,
    smoothOneFormL2Pairing_smul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 Hilbert completion of smooth covariant one-forms.
The completion uses the definite intrinsic metric pairing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneForm_inner_eq (u v : SmoothL2OneForm o) :
    inner ℝ u v = smoothOneFormL2Pairing (o := o) u v := rfl

theorem smoothOneFormToL2_dense : DenseRange (smoothOneFormToL2 (o := o)) :=
  UniformSpace.Completion.denseRange_coe

theorem smoothOneFormToL2_injective : Function.Injective (smoothOneFormToL2 (o := o)) :=
  (smoothOneFormToL2 (o := o)).injective

theorem smoothOneFormToL2_inner (u v : SmoothL2OneForm o) :
    inner ℝ (smoothOneFormToL2 u) (smoothOneFormToL2 v) =
      smoothOneFormL2Pairing (o := o) u v :=
  UniformSpace.Completion.inner_coe u v

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous mean and its kernel on the actual scalar first-jet
completion.  Mean subtraction changes only the value coordinate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

section FirstJet

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

variable [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

instance scalarH1MeanZero_complete (d : ParallelMetricData g μ) :
    CompleteSpace (scalarH1MeanZero d) :=
  (scalarH1MeanZero_closed d).isComplete.completeSpace_coe

end FirstJet

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth functions as degree-zero covariant fields and their actual
one-form differential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem smoothScalarDifferential_derivative (f : SmoothScalar (M := M))
    (e : FrameBundle g) (i j : Fin 4) :
    covariantFieldFramed g (covariantFieldDerivative g (smoothScalarDifferential g f).val)
      e ![i,j] = scalarHessian g f.val e i j := by
  have h := (smoothScalarCovariantField f).property.framed_second (g := g) e
  rw [smoothScalarCovariantField_coordinates] at h
  exact congrFun h ![i,j]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differential of an actual smooth scalar is a closed one-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothScalarDifferential_closed (f : SmoothScalar (M := M)) :
    smoothOneFormExterior (o := o) (smoothScalarDifferential g f) = 0 := by
  have hz (e : FrameBundle g) : twoFormFramedValue o
      (smoothOneFormExterior (o := o) (smoothScalarDifferential g f)).val e = 0 := by
    funext a
    have ha : a = ![a 0,a 1] := by ext k; fin_cases k <;> rfl
    rw [ha, smoothOneFormExterior_framed, smoothScalarDifferential_derivative,
      smoothScalarDifferential_derivative, actual_scalarHessian_symmetric f.property e (a 0) (a 1)]
    simp only [sub_self, Pi.zero_apply]
  apply Subtype.ext
  funext x
  apply twoFormTensor_injective
  have h := hz ⟨x,o.frame x⟩
  rw [twoFormFramedValue_eq, twoFormFrameValue_at_orientation] at h
  exact h.trans (map_zero twoFormTensorLinear).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth Poincaré estimate passes to the actual first-jet completion.
It makes the Dirichlet form coercive on the closed mean-zero subspace and
therefore supplies a unique mean-zero weak Poisson solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarCoercive_h1Space
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarCoercive_meanZeroSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarCoercive_h1Inner
local instance scalarCoercive_meanZeroInner (d : ParallelMetricData g μ) :
    InnerProductSpace ℝ (scalarH1MeanZero d) := Submodule.innerProductSpace _

/-- The Poincaré estimate controls the full first-jet norm on the mean-zero
subspace; the coercivity constant is exactly `1 / (K + 1)`. -/
theorem scalarMeanZeroDirichlet_coercive (d : ParallelMetricData g μ)
    {K : ℝ} (hK : 0 < K) (hP : SmoothScalarPoincare d K) :
    @IsCoercive (scalarH1MeanZero d) _ (scalarCoercive_meanZeroSpace d)
      (scalarMeanZeroDirichlet d) := by
  have hK₁ : 0 < K + 1 := by linarith
  refine ⟨1 / (K + 1), one_div_pos.mpr hK₁, ?_⟩
  intro u
  have hu := scalarH1_poincare d hP u.val u.property
  have hn := scalarH1_norm_sq d u.val
  have hbound : ‖u‖ ^ 2 ≤ (K + 1) *
      (∑ i : Fin 4, ‖scalarH1Gradient d i u.val‖ ^ 2) := by
    change ‖u.val‖ ^ 2 ≤ _
    nlinarith only [hu, hn]
  rw [scalarMeanZeroDirichlet_self]
  have heq : (1 / (K + 1)) * ‖u‖ * ‖u‖ = ‖u‖ ^ 2 / (K + 1) := by ring
  rw [heq]
  exact (div_le_iff₀ hK₁).mpr (by simpa only [mul_comm] using hbound)

/-- The unique mean-zero weak solution, as a continuous operator on `L²`.
Its sign convention is the positive Dirichlet operator `-Δ`. -/
def scalarMeanZeroWeakPoisson (d : ParallelMetricData g μ) {K : ℝ}
    (hK : 0 < K) (hP : SmoothScalarPoincare d K) :
    ScalarL2 g μ →L[ℝ] scalarH1MeanZero d :=
  @fourGradientSolution (scalarH1MeanZero d) (ScalarL2 g μ)
    _ (scalarCoercive_meanZeroInner d) (scalarH1MeanZero_complete d) _ _ _
    (scalarMeanZeroGradient d) (scalarMeanZeroValue d)
    (scalarMeanZeroDirichlet_coercive d hK hP)

theorem scalarMeanZeroWeakPoisson_weak (d : ParallelMetricData g μ) {K : ℝ}
    (hK : 0 < K) (hP : SmoothScalarPoincare d K) (f : ScalarL2 g μ)
    (v : scalarH1MeanZero d) :
    (∑ i : Fin 4, inner ℝ
      (scalarH1Gradient d i (scalarMeanZeroWeakPoisson d hK hP f).val)
      (scalarH1Gradient d i v.val)) = inner ℝ f (scalarH1Value d v.val) := by
  exact @fourGradientSolution_weak (scalarH1MeanZero d) (ScalarL2 g μ)
    _ (scalarCoercive_meanZeroInner d) (scalarH1MeanZero_complete d) _ _ _
    (scalarMeanZeroGradient d) (scalarMeanZeroValue d)
    (scalarMeanZeroDirichlet_coercive d hK hP) f v

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity for the actual first-jet completion.  This identifies
the variational equation with the distributional scalar Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

/-- The first-jet completion has no nonzero element with zero scalar value:
Green's identity determines every derivative coordinate. -/
theorem scalarH1Value_injective (d : ParallelMetricData g μ) :
    Function.Injective (scalarH1Value d) := by
  intro u v huv
  apply scalarH1_eq_of_smooth_tests d
  intro b
  rw [scalarH1_inner, scalarH1_inner]
  simp only [scalarH1Value_smooth, scalarH1Gradient_smooth]
  rw [scalarH1_green d u b, scalarH1_green d v b, huv]

theorem scalarH1_eq_smooth_of_value (d : ParallelMetricData g μ)
    (u : scalarH1 d) (a : SmoothScalar (M := M))
    (hu : scalarH1Value d u = smoothScalarValueL2 g μ a) :
    u = smoothScalarToH1 d a :=
  scalarH1Value_injective d hu

end
end PositiveEinsteinFour.Geometry
end


section

/-! The divergence of an actual smooth one-form is a smooth scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem oneFormDivergence_differential (f : SmoothScalar (M := M)) (e : FrameBundle g) :
    oneFormDivergence g (smoothScalarDifferential g f) e.base = scalarLaplacian g f.val e := by
  rw [oneFormDivergence_eq_frame]
  apply Finset.sum_congr rfl
  intro i _
  exact smoothScalarDifferential_derivative f e i i

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the actual exterior derivative of one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_3
omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothOneFormExterior_frame_pairing (u : smoothCovariantFields M 1)
    (v : smoothTwoForms o) (e : FrameBundle g) :
    inner ℝ (twoFormFrameValue o (smoothOneFormExterior (o := o) u).val e)
      (twoFormFrameValue o v.val e) =
      ∑ i, ∑ j, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j] *
        twoFormFramedValue o v.val e ![i,j] := by
  have hp := twoCovariantAlternation_pairing
    (covariantFieldFramed g (covariantFieldDerivative g u.val) e)
    (twoFormFramedValue o v.val e) (twoFormFramedValue_skew v.val e)
  rw [← smoothOneFormExterior_framed_tensor (o := o) u e, twoFormFramedValue_eq,
    twoFormFramedValue_eq, twoFormTensor_pairing] at hp
  rw [← twoFormFramedValue_eq o v.val e] at hp
  linarith only [hp]

theorem smoothOneForm_direction_green (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (v : smoothTwoForms o) (i j : Fin 4) :
    (∫ e, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j] *
      twoFormFramedValue o v.val e ![i,j] ∂canonicalFrameMeasure g o) =
      -(∫ e, covariantFieldFramed g u.val e ![j] *
        twoFormFramedCovariantDerivative o v.val e ![i,i,j] ∂canonicalFrameMeasure g o) := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => covariantFieldFramed g u.val e ![j],
    (continuous_apply _).comp u.property.continuous_framed⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j],
    (continuous_apply _).comp u.property.derivative.continuous_framed⟩
  let H : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedValue o v.val e ![i,j],
    (continuous_apply _).comp v.property.continuous_framedValue⟩
  let DH : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedCovariantDerivative o v.val e ![i,i,j],
    (continuous_apply _).comp v.property.continuous_framedCovariantDerivative⟩
  apply scalar_flow_green (d := d.toMetricGreenData) i F DF H DH
  · intro t e
    exact u.property.parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![j]
  · intro t e
    exact v.property.framedValue_parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![i,j]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual L2 sections obtained from continuous frame tensors, together
with their exact pairings against smooth two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_4
theorem twoFormFromTensorL2_norm_le (F : Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o)) :
    ‖twoFormFromTensorL2 F‖ ≤ ‖F‖ := by
  let w := twoFormFromTensorL2 F
  have hT : ‖twoFormTensorL2 w‖ ≤ 2 * ‖w‖ := by
    nlinarith [twoFormTensorL2_norm_sq w, norm_nonneg w, norm_nonneg (twoFormTensorL2 w)]
  have hi := (le_abs_self (inner ℝ F (twoFormTensorL2 w))).trans
    (abs_real_inner_le_norm F (twoFormTensorL2 w))
  have hb := mul_le_mul_of_nonneg_left hT (norm_nonneg F)
  have he : ‖w‖ ^ 2 = (1 / 2 : ℝ) * inner ℝ F (twoFormTensorL2 w) := by
    rw [← real_inner_self_eq_norm_sq]
    exact twoFormFromTensorL2_pairing F w
  by_cases hw : ‖w‖ = 0
  · change ‖w‖ ≤ ‖F‖
    rw [hw]
    exact norm_nonneg _
  · have hwpos := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    change ‖w‖ ≤ ‖F‖
    nlinarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The index density in an actual metric chart equals the normal Euclidean
Jacobi index density when evaluated in a parallel orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChart_normal_curvature_vector (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (a : Fin 3 → ℝ) :
    jacobiCurvature (fun i => connectionMatrix g c i (chartAt FourSpace c e.base))
        (fun i j => matrixPartial (connectionMatrix g c j) i (chartAt FourSpace c e.base))
        (frameChartMatrix g c e *ᵥ Fin.cons 0 a) (fun i => frameChartMatrix g c e i 0) *ᵥ
          (fun i => frameChartMatrix g c e i 0) =
      frameChartMatrix g c e *ᵥ Fin.cons 0 ((1 + frameCurvatureField g e) *ᵥ a) := by
  let E := frameChartMatrix g c e
  have hdet : IsUnit E.det :=
    Matrix.isUnit_det_of_left_inverse (frameChartMatrix_normalizes g c e he)
  have h := congrArg (fun v => E *ᵥ v)
    (frameChart_normal_jacobi_curvature g c e he (Fin.cons 0 a))
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  simpa only [actual_jacobiCurvature_eq, jacobiCurvatureCombination, Fin.cons_succ] using h

/-- Only the ordinary-to-covariant derivative relation is needed in addition
to the actual frame and curvature. -/
theorem actual_coordinateIndexDensity_normal (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (a b : Fin 3 → ℝ) (w : JacobiCoordinateVector)
    (hw : w + jacobiConnection
        (fun i => connectionMatrix g c i (chartAt FourSpace c e.base))
        (fun i => frameChartMatrix g c e i 0) *ᵥ
          (frameChartMatrix g c e *ᵥ Fin.cons 0 a) =
      frameChartMatrix g c e *ᵥ Fin.cons 0 b) :
    coordinateIndexDensity (metricInChart g c (chartAt FourSpace c e.base))
        (fun i => connectionMatrix g c i (chartAt FourSpace c e.base))
        (fun i j => matrixPartial (connectionMatrix g c j) i (chartAt FourSpace c e.base))
        (fun i => frameChartMatrix g c e i 0) (frameChartMatrix g c e *ᵥ Fin.cons 0 a) w =
      normalIndexDensity (1 + frameCurvatureField g e) a b := by
  unfold coordinateIndexDensity
  rw [hw, frameChart_normal_curvature_vector g c e he,
    jacobiMetricPair_frame _ _ (frameChartMatrix_normalizes g c e he),
    jacobiMetricPair_frame _ _ (frameChartMatrix_normalizes g c e he),
    normal_lift_dotProduct, normal_lift_dotProduct]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Normal fields along the actual parallel-frame flow.  Their ordinary
coordinate derivatives and their index densities are derived from the
constructed horizontal ODE, rather than supplied as extra field identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

/-- The actual coordinate index is the matrix index for every prescribed
normal value and normal derivative; the ordinary derivative is constructed. -/
theorem normalChartField_index (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (a b : ℝ → Fin 3 → ℝ) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    chartEnergyIndexDensity g c (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
      (fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) i 0)
      (normalChartField g c e a t) (normalChartFieldRate g c e a b t) =
    normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (a t) (b t) := by
  apply actual_coordinateIndexDensity_normal g c (parallelFrameFlowMap g 0 t e) hc
  rw [normalChartFieldRate_eq]
  exact sub_add_cancel _ _

theorem normalChartField_index_continuousOn (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (S : Set ℝ)
    (hc : ∀ t ∈ S, (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : ContinuousOn a S) (hb : ContinuousOn b S) :
    ContinuousOn (fun t =>
      chartEnergyIndexDensity g c (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
        (fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) i 0)
        (normalChartField g c e a t) (normalChartFieldRate g c e a b t)) S := by
  have hR : Continuous (fun t =>
      (1 : NormalMatrix) + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) :=
    continuous_const.add ((actual_frameCurvature_continuous g hRic).comp
      (parallelFrameFlowMap_curve_continuous g 0 e))
  have hN : ContinuousOn (fun t => normalIndexDensity
      (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (a t) (b t)) S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (hb.domRestrict.dotProduct hb.domRestrict).sub
      (((hR.comp continuous_subtype_val).matrix_mulVec ha.domRestrict).dotProduct ha.domRestrict)
  apply hN.congr
  intro t ht
  exact normalChartField_index g c e a b t (hc t ht)

theorem normalChartField_index_intervalIntegrable (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ) (s t : ℝ)
    (hc : ∀ r ∈ uIcc s t,
      (parallelFrameFlowMap g 0 r e).base ∈ (chartAt FourSpace c).source)
    (ha : ContinuousOn a (uIcc s t)) (hb : ContinuousOn b (uIcc s t)) :
    IntervalIntegrable (fun r =>
      chartEnergyIndexDensity g c (chartAt FourSpace c (parallelFrameFlowMap g 0 r e).base)
        (fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 r e) i 0)
        (normalChartField g c e a r) (normalChartFieldRate g c e a b r))
      MeasureTheory.volume s t :=
  (normalChartField_index_continuousOn g hRic c e a b (uIcc s t) hc ha hb).intervalIntegrable

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second variation on a fixed-chart segment of the actual unit
geodesic.  The position, velocity and normal-field derivatives are obtained
from the constructed flow; only the prescribed second jet is differentiated
as input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped _root_.Topology Manifold ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem normalChartField_second_integral (g : SmoothMetric M) (hRic : RicciThree g)
    (c : M) (e : FrameBundle g) (a b : ℝ → Fin 3 → ℝ)
    (u q : ℝ → JacobiCoordinateVector) (r s : ℝ)
    (hc : ∀ t ∈ uIcc r s,
      (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source)
    (ha : ∀ t ∈ uIcc r s, HasDerivAt a (b t) t)
    (hb : ContinuousOn b (uIcc r s))
    (hu : ∀ t ∈ uIcc r s, HasDerivAt u (q t) t)
    (hS : IntervalIntegrable (fun t => chartEnergySecondDensity g c
      (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
      (normalChartField g c e a t) (geodesicChartVelocity g c e t)
      (normalChartFieldRate g c e a b t) (u t) (q t)) volume r s) :
    (∫ t in r..s, chartEnergySecondDensity g c
      (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
      (normalChartField g c e a t) (geodesicChartVelocity g c e t)
      (normalChartFieldRate g c e a b t) (u t) (q t)) =
        (∫ t in r..s, normalIndexDensity
          (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (a t) (b t)) +
        chartEnergyBoundary g c
          (chartAt FourSpace c (parallelFrameFlowMap g 0 s e).base)
          (geodesicChartVelocity g c e s) (normalChartField g c e a s) (u s) -
        chartEnergyBoundary g c
          (chartAt FourSpace c (parallelFrameFlowMap g 0 r e).base)
          (geodesicChartVelocity g c e r) (normalChartField g c e a r) (u r) := by
  have hac : ContinuousOn a (uIcc r s) := fun t ht =>
    (ha t ht).continuousAt.continuousWithinAt
  have hI := normalChartField_index_intervalIntegrable g hRic c e a b r s hc hac hb
  have h := chartEnergySecond_integral g c
    (fun t => chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
    (geodesicChartVelocity g c e) (normalChartField g c e a)
    (normalChartFieldRate g c e a b) u q r s
    (fun t ht => (chartAt FourSpace c).map_source (hc t ht))
    (fun t ht => geodesicChartPosition_hasDerivAt g c e t (hc t ht))
    (fun t ht => geodesicChartVelocity_hasDerivAt g c e t (hc t ht))
    (fun t ht => normalChartField_hasDerivAt g c e a b t (hc t ht) (ha t ht))
    hu hS hI
  have hindex :
      (∫ t in r..s, chartEnergyIndexDensity g c
        (chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base)
        (geodesicChartVelocity g c e t) (normalChartField g c e a t)
        (normalChartFieldRate g c e a b t)) =
      ∫ t in r..s, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (a t) (b t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact normalChartField_index g c e a b t (hc t ht)
  rw [hindex] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Normal-coordinate balls with a C1 inverse, constructed from the actual
exponential and the openness of invertible derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_normal_ball (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ (r : ℝ) (C : OpenPartialHomeomorph FourSpace M), 0 < r ∧
      C.source = ball 0 r ∧ EqOn C (frameExponential g o e) C.source ∧
      ContMDiffOn I4 I4 1 C.symm C.target := by
  let : CompleteSpace FourSpace := inferInstance
  obtain ⟨D, hzero, hD⟩ := frameExponential_localChart g o e
  let F := fun v : FourSpace => chartAt FourSpace e.base (frameExponential g o e v)
  have hF : ContDiffAt ℝ 1 F 0 := frameExponential_chart_contDiffAt_zero g o e.base e
    (mem_chart_source FourSpace e.base)
  have hunit : IsUnit (fderiv ℝ F 0) := by
    have hd := frameExponential_chart_strictDerivative_zero g o e.base e
      (mem_chart_source FourSpace e.base)
    rw [hd.hasFDerivAt.fderiv]
    simpa only [chartForwardOperator_center, ContinuousLinearMap.id_comp] using
      frameMap_isUnit g e
  have hnearE : ∀ᶠ v in 𝓝 (0 : FourSpace),
      fderiv ℝ F v ∈ range ((↑) : (FourSpace ≃L[ℝ] FourSpace) →
        FourSpace →L[ℝ] FourSpace) :=
    (hF.continuousAt_fderiv one_ne_zero).preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds
        ⟨ContinuousLinearEquiv.ofUnit hunit.unit, hunit.unit_spec⟩)
  have hnear : ∀ᶠ v in 𝓝 (0 : FourSpace), IsUnit (fderiv ℝ F v) := by
    filter_upwards [hnearE] with v hv
    obtain ⟨E, hE⟩ := hv
    exact hE ▸ E.toUnit.isUnit
  have hbase : frameExponential g o e 0 ∈ (chartAt FourSpace e.base).source := by
    rw [frameExponential_zero]
    exact mem_chart_source FourSpace e.base
  have hchart := (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
    ((chartAt FourSpace e.base).open_source.mem_nhds hbase)
  have hgood : {v : FourSpace | v ∈ D.source ∧
      frameExponential g o e v ∈ (chartAt FourSpace e.base).source ∧
      IsUnit (fderiv ℝ F v)} ∈ 𝓝 0 := by
    filter_upwards [D.open_source.mem_nhds hzero, hchart, hnear] with v hv hc hu
    exact ⟨hv, hc, hu⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgood
  let C := D.restrOpen (ball 0 r) isOpen_ball
  have hsource : C.source = ball 0 r := by
    change D.source ∩ ball 0 r = ball 0 r
    exact inter_eq_right.mpr (fun v hv => (hball hv).1)
  have hC : EqOn C (frameExponential g o e) C.source := fun _ hv => hD hv.1
  refine ⟨r, C, hr, hsource, hC, ?_⟩
  intro y hy
  let v := C.symm y
  have hv : v ∈ C.source := C.map_target hy
  have hvg := hball (hsource ▸ hv)
  have heq : frameExponential g o e v = y := (hC hv).symm.trans (C.right_inv hy)
  have hc := frameExponential_chart_local_inverse_contMDiffAt g o e e.base v C hv hC
    hvg.2.1 hvg.2.2
  rw [heq] at hc
  exact hc.contMDiffWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous family of normal tensors with one compact support
lifts to a jointly continuous family on the actual frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] {g : SmoothMetric M} {c : M}

theorem heatNormalOneFrameLift_joint_continuous
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (T : ℝ → FourSpace → CovariantCoordinates 1)
    (hT : ContinuousOn (fun z : ℝ × FourSpace => T z.1 z.2) (Ioi 0 ×ˢ C.source))
    (K : Set FourSpace) (hK : IsCompact K) (hKC : K ⊆ C.source)
    (hs : ∀ t > 0, tsupport (T t) ⊆ K) :
    ContinuousOn (fun z : ℝ × FrameBundle g => heatNormalOneFrameLift g c C (T z.1) z.2)
      (Ioi 0 ×ˢ univ) := by
  have hCK : IsCompact (C '' K) := hK.image_of_continuousOn (C.continuousOn.mono hKC)
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have hbase : Continuous (fun w : ℝ × FrameBundle g => w.2.base) :=
    (continuous_frameBase g).comp continuous_snd
  by_cases he : z.2.base ∈ C.target
  · have hinv : ContinuousAt (fun w : ℝ × FrameBundle g => C.symm w.2.base) z :=
      ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => w.2.base) (x := z)
        (C.continuousOn_symm.continuousAt (C.open_target.mem_nhds he)) hbase.continuousAt
    have harg : ContinuousAt (fun w : ℝ × FrameBundle g => (w.1, C.symm w.2.base)) z :=
      continuousAt_fst.prodMk hinv
    have hTc : ContinuousAt (fun w : ℝ × FourSpace => T w.1 w.2) (z.1, C.symm z.2.base) :=
      hT.continuousAt ((isOpen_Ioi.prod C.open_source).mem_nhds
        (show (z.1, C.symm z.2.base) ∈ Ioi (0 : ℝ) ×ˢ C.source from ⟨hz.1, C.map_target he⟩))
    have hval : ContinuousAt (fun w : ℝ × FrameBundle g => T w.1 (C.symm w.2.base)) z :=
      ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => (w.1, C.symm w.2.base))
        (x := z) hTc harg
    have hframe : ContinuousAt (fun w : ℝ × FrameBundle g =>
        frameTensor (frameChartMatrix g c w.2) (T w.1 (C.symm w.2.base))) z := by
      apply continuousAt_pi.mpr
      intro a
      unfold frameTensor
      apply tendsto_finsetSum
      intro b _
      exact (tendsto_finsetProd _ (fun k _ =>
        ContinuousAt.comp (f := fun w : ℝ × FrameBundle g => w.2) (x := z)
          (frameChartMatrix_continuousAt g c z.2 (hCt he) (b k) (a k)) continuousAt_snd)).mul
        ((continuous_apply b).continuousAt.comp hval)
    apply hframe.congr_of_eventuallyEq
    have hn := hbase.continuousAt.eventually
      (C.open_target.mem_nhds he)
    filter_upwards [hn] with w hw
    exact ite_eq_left hw
  · have hnot : z.2.base ∉ C '' K := by
      rintro ⟨x, hx, hxe⟩
      exact he (hxe ▸ C.map_source (hKC hx))
    apply (continuousAt_const (y := (0 : CovariantCoordinates 1))).congr_of_eventuallyEq
    have hn := hbase.continuousAt.eventually
      (hCK.isClosed.isOpen_compl.mem_nhds hnot)
    have ht : ∀ᶠ w : ℝ × FrameBundle g in 𝓝 z, 0 < w.1 :=
      continuousAt_fst.eventually (Ioi_mem_nhds hz.1)
    filter_upwards [hn, ht] with w hw hwt
    apply not_ne_iff.mp
    intro hne
    obtain ⟨x, hx, hxe⟩ := heatNormalOneFrameLift_support g c C (T w.1) hne
    exact hw ⟨x, hs w.1 hwt hx, hxe⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual coordinate tensor reconstructed
from a time-dependent normal amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCoordinates_joint_continuous
    (C : OpenPartialHomeomorph FourSpace M)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (A : ℝ → FourSpace → FourSpace)
    (hA : ContinuousOn (fun z : ℝ × FourSpace => A z.1 z.2) (Ioi 0 ×ˢ C.source)) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalOneCoordinates D (A z.1) z.2)
      (Ioi 0 ×ˢ C.source) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have hPx := hP.contDiffAt (C.open_source.mem_nhds hz.2)
  have hE (i j : Fin 4) : ContDiffAt ℝ 2 (fun y => (D.point y).2 i j) z.2 :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hPx.snd i) j
  have hEi (i j : Fin 4) : ContinuousAt (fun w : ℝ × FourSpace => (D.point w.2).2⁻¹ i j) z :=
    (heatMatrixInverse_contDiffAt 2 (fun y => (D.point y).2) z.2 hE
      (heatNormalFrame_matrix_nondegenerate D (hD hz.2)) i j).continuousAt.comp continuousAt_snd
  have hAc := hA.continuousAt ((isOpen_Ioi.prod C.open_source).mem_nhds hz)
  apply continuousAt_pi.mpr
  intro v
  change ContinuousAt (fun w : ℝ × FourSpace =>
    ∑ b : Fin 1 → Fin 4, (∏ k, (D.point w.2).2⁻¹ (b k) (v k)) * A w.1 w.2 (b 0)) z
  apply tendsto_finsetSum
  intro b _
  exact (tendsto_finsetProd _ (fun k _ => hEi (b k) (v k))).mul
    ((EuclideanSpace.proj (b 0) : FourSpace →L[ℝ] ℝ).continuous.continuousAt.comp hAc)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential differential is arbitrarily close to an
isometry near zero, uniformly in the tangent direction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_metric_differential_zero (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (w : FourSpace) :
    metricTangentNorm g (frameExponential g o e 0)
      (mfderiv I4 I4 (frameExponential g o e) 0 w) = ‖w‖ := by
  have hd := frameExponential_chart_strictDerivative_zero g o e.base e
    (mem_chart_source FourSpace e.base)
  have hzero : fderiv ℝ (fun v : FourSpace => chartAt FourSpace e.base
      (frameExponential g o e v)) 0 = e.frame.map.toContinuousLinearMap := by
    simpa only [chartForwardOperator_center, ContinuousLinearMap.id_comp] using hd.hasFDerivAt.fderiv
  have hc := frameExponential_center_fderiv g o e 0
  rw [frameExponential_zero] at hc
  have hm : mfderiv I4 I4 (frameExponential g o e) 0 w = e.frame.map w := by
    exact (congrArg (fun L : FourSpace →L[ℝ] FourSpace => L w) hc).symm.trans
      (congrArg (fun L : FourSpace →L[ℝ] FourSpace => L w) hzero)
  let u : FourSpace := mfderiv I4 I4 (frameExponential g o e) 0 w
  change metricTangentNorm g (frameExponential g o e 0) u = ‖w‖
  have hu : u = e.frame.map w := hm
  have hn : metricTangentNorm g e.base (show TangentSpace I4 e.base from e.frame.map w) =
      ‖w‖ := by
    have hh := metricTangentNorm_eq_sqrt g e.base
      (show TangentSpace I4 e.base from e.frame.map w)
    simpa only [e.frame.inner_map_self, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg w)] using! hh
  rw [hu, frameExponential_zero]
  exact hn

theorem frameExponential_differential_norm_near (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ v in 𝓝 (0 : FourSpace), ∀ w : FourSpace,
      metricTangentNorm g (frameExponential g o e v)
        (mfderiv I4 I4 (frameExponential g o e) v w) ≤ (1 + ε) * ‖w‖ := by
  let B : FourSpace → FourSpace → ℝ := fun v w => metricTangentNorm g (frameExponential g o e v)
    (mfderiv I4 I4 (frameExponential g o e) v w)
  have hunit : ∀ᶠ v in 𝓝 (0 : FourSpace), ∀ w ∈ sphere (0 : FourSpace) 1,
      B v w < 1 + ε := by
    apply (isCompact_sphere (0 : FourSpace) 1).eventually_forall_of_forall_eventually
    intro w hw
    have hn : ‖w‖ = 1 := by simpa using hw
    have hc := (frameExponential_metric_differential_continuous g o e).continuousAt
      (x := ((0 : FourSpace), w))
    apply hc.eventually_lt continuousAt_const
    change B 0 w < 1 + ε
    dsimp [B]
    rw [frameExponential_metric_differential_zero, hn]
    linarith
  have hscale (v w : FourSpace) (r : ℝ) : B v (r • w) = |r| * B v w := by
    dsimp [B]
    have hm := (mfderiv I4 I4 (frameExponential g o e) v).map_smul r
      (show TangentSpace I4 v from w)
    have hh := congrArg (metricTangentNorm g (frameExponential g o e v)) hm
    apply hh.trans
    let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
    change ‖r • mfderiv I4 I4 (frameExponential g o e) v w‖ =
      |r| * ‖mfderiv I4 I4 (frameExponential g o e) v w‖
    rw [norm_smul, Real.norm_eq_abs]
  filter_upwards [hunit] with v hv
  intro w
  by_cases hw : w = 0
  · subst w
    have hz : B v 0 = 0 := by
      have h := hscale v (0 : FourSpace) 0
      simpa only [zero_smul, abs_zero, zero_mul] using! h
    change B v 0 ≤ _
    rw [hz, norm_zero, mul_zero]
  · let q : FourSpace := ‖w‖⁻¹ • w
    have hq : ‖q‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg w),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
    have hwq : ‖w‖ • q = w := by
      dsimp [q]
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hw), one_smul]
    change B v w ≤ (1 + ε) * ‖w‖
    calc
      B v w = ‖w‖ * B v q := by
        conv_lhs => rw [← hwq]
        rw [hscale, abs_of_nonneg (norm_nonneg w)]
      _ ≤ ‖w‖ * (1 + ε) := mul_le_mul_of_nonneg_left
        (hv q (by simpa using hq)).le (norm_nonneg w)
      _ = _ := mul_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Sharp local distance bounds for the actual exponential. These bounds
will exclude corners in distance-minimizing concatenations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_locally_almost_isometric (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > (0 : ℝ), ∀ u ∈ Metric.ball (0 : FourSpace) r,
      ∀ v ∈ Metric.ball (0 : FourSpace) r,
      metricEDistance g (frameExponential g o e u) (frameExponential g o e v) ≤
        ENNReal.ofReal (1 + ε) * edist u v := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (frameExponential_differential_norm_near g o e ε hε)
  let K : ℝ≥0 := ⟨1 + ε, by positivity⟩
  refine ⟨r, hr, fun u hu v hv => ?_⟩
  have h := frameExponential_distance_le_of_differential g o e _
    (convex_ball (0 : FourSpace) r) K (fun z hz w => hball hz w) u v hu hv
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal (1 + ε) := ENNReal.coe_nnreal_eq K
  rw [hK] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine corner between two radial geodesics can be shortened. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_corner_shortening (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (u v : FourSpace)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) :
    ∃ r > (0 : ℝ), ∀ t : ℝ, 0 < t → t < r →
      metricEDistance g (frameExponential g o e ((-t) • u))
        (frameExponential g o e (t • v)) < ENNReal.ofReal (2 * t) := by
  have hsum : ‖u + v‖ < 2 := by
    have hle : ‖u + v‖ ≤ 2 := by simpa only [hu, hv, one_add_one_eq_two] using norm_add_le u v
    apply lt_of_le_of_ne hle
    intro heq
    apply huv
    have hadd : ‖u + v‖ = ‖u‖ + ‖v‖ := by simpa only [hu, hv, one_add_one_eq_two] using heq
    simpa only [hu, hv, one_smul] using norm_add_eq_iff_real.mp hadd
  let ε := (2 - ‖u + v‖) / 4
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hfac : (1 + ε) * ‖u + v‖ < 2 := by
    have hp : 0 < (2 - ‖u + v‖) * (4 - ‖u + v‖) :=
      mul_pos (by linarith) (by linarith)
    dsimp [ε]
    nlinarith
  obtain ⟨r, hr, hbound⟩ := frameExponential_locally_almost_isometric g o e ε hε
  refine ⟨r, hr, fun t ht htr => ?_⟩
  have hleft : (-t) • u ∈ ball (0 : FourSpace) r := by
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_pos ht, hu, mul_one] using htr
  have hright : t • v ∈ ball (0 : FourSpace) r := by
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, hv, mul_one] using htr
  have hd : edist ((-t) • u) (t • v) = ENNReal.ofReal (t * ‖u + v‖) := by
    have heq : (-t) • u - t • v = (-t) • (u + v) := by
      rw [smul_add, neg_smul, neg_smul]
      abel
    rw [edist_eq_enorm_sub, ← ofReal_norm, heq, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_pos ht]
  have h := hbound ((-t) • u) hleft (t • v) hright
  rw [hd, ← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 + ε)] at h
  apply h.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * t)).mpr
  nlinarith [mul_lt_mul_of_pos_right hfac ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A distance-minimizing concatenation of radial geodesics has matching
incoming and outgoing tangent directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Bundle Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_no_minimizing_corner (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (u v : FourSpace)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmin : metricEDistance g (frameExponential g o e ((-a) • u))
      (frameExponential g o e (b • v)) = ENNReal.ofReal (a + b)) : u = v := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  by_contra huv
  obtain ⟨r, hr, hshort⟩ := frameExponential_corner_shortening g o e u v hu hv huv
  let t := min r (min a b) / 2
  have hm : 0 < min r (min a b) := lt_min hr (lt_min ha hb)
  have ht : 0 < t := half_pos hm
  have htm : t < min r (min a b) := half_lt_self hm
  have htr : t < r := htm.trans_le (min_le_left _ _)
  have hta : t < a := htm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htb : t < b := htm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  let qneg : Directions := ⟨-u, by simpa only [norm_neg] using hu⟩
  let qpos : Directions := ⟨v, hv⟩
  have hleft : metricEDistance g (frameExponential g o e ((-a) • u))
      (frameExponential g o e ((-t) • u)) ≤ ENNReal.ofReal (a - t) := by
    simpa only [qneg, smul_neg, neg_smul, abs_of_nonpos (sub_nonpos.mpr hta.le), neg_sub]
      using frameExponential_ray_distance g o e qneg a t ha ht
  have hright : metricEDistance g (frameExponential g o e (t • v))
      (frameExponential g o e (b • v)) ≤ ENNReal.ofReal (b - t) := by
    simpa only [qpos, abs_of_nonneg (sub_nonneg.mpr htb.le)]
      using frameExponential_ray_distance g o e qpos t b ht hb
  have hmid := hshort t ht htr
  let A := frameExponential g o e ((-a) • u)
  let B := frameExponential g o e (b • v)
  let L := frameExponential g o e ((-t) • u)
  let R := frameExponential g o e (t • v)
  have htri : metricEDistance g A B ≤ metricEDistance g A L +
      (metricEDistance g L R + metricEDistance g R B) :=
    (Manifold.riemannianEDist_triangle (I := I4) (x := A) (y := L) (z := B)).trans
      (add_le_add le_rfl (Manifold.riemannianEDist_triangle (I := I4) (x := L) (y := R) (z := B)))
  have hbound : ENNReal.ofReal (a + b) ≤ ENNReal.ofReal (a - t) +
      (metricEDistance g L R + ENNReal.ofReal (b - t)) := by
    rw [← hmin]
    exact htri.trans (add_le_add hleft (add_le_add le_rfl hright))
  have hs := ENNReal.add_lt_add_left (a := ENNReal.ofReal (a - t)) ENNReal.ofReal_ne_top
    (ENNReal.add_lt_add_right (a := ENNReal.ofReal (b - t)) ENNReal.ofReal_ne_top hmid)
  have heq : ENNReal.ofReal (a - t) + (ENNReal.ofReal (2 * t) + ENNReal.ofReal (b - t)) =
      ENNReal.ofReal (a + b) := by
    rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 2 * t) (by linarith : 0 ≤ b - t),
      ← ENNReal.ofReal_add (by linarith : 0 ≤ a - t) (by linarith : 0 ≤ 2 * t + (b - t))]
    congr 1
    ring
  rw [heq] at hs
  exact (not_lt_of_ge hbound) hs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Time reversal of the actual complete geodesic, using the oriented
frame rotation by minus the identity in dimension four. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M]

theorem frameExponential_first_ray_neg (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) :
    frameExponential g o e ((-t) • coordinateVector 0) = frameGeodesic g 0 e (-t) := by
  have hp : frameAntipode g e ∈ o.positive := frameRotate_oriented_positive o e he _
  have hL : orthogonalEuclideanIsometry (orientedToOrthogonal reverseFrameRotation).val
      (orientedToOrthogonal reverseFrameRotation).property (t • coordinateVector 0) =
        (-t) • coordinateVector 0 := by
    ext i
    change ((orientedToOrthogonal reverseFrameRotation).val *ᵥ
      WithLp.ofLp (t • coordinateVector 0)) i = _
    rw [reverseFrameRotation_matrix, Matrix.neg_mulVec, Matrix.one_mulVec]
    simp
  rw [← hL, ← frameExponential_rotate]
  change frameExponential g o (frameAntipode g e) (t • coordinateVector 0) = _
  rw [frameExponential_first_ray g o _ hp t ht]
  exact (congrArg FrameBundle.base (parallelFrameFlowMap_antipode g 0 t e)).symm

theorem frameExponential_first_ray_all (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    frameExponential g o e (t • coordinateVector 0) = frameGeodesic g 0 e t := by
  rcases lt_trichotomy 0 t with ht | ht | ht
  · exact frameExponential_first_ray g o e he t ht
  · subst t
    simp only [zero_smul, frameExponential_zero, frameGeodesic, parallelFrameFlowMap_zero]
  · simpa only [neg_neg] using frameExponential_first_ray_neg g o e he (-t) (neg_pos.mpr ht)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A minimizing radial segment that splits the distance to an exterior
point continues a positive distance along the same complete geodesic. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [PreconnectedSpace M] in
theorem frameExponential_shift_first (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (s t : ℝ) :
    frameExponential g o (parallelFrameFlowMap g 0 t e) (s • coordinateVector 0) =
      frameGeodesic g 0 e (s + t) := by
  rw [frameExponential_first_ray_all g o _ (parallelFrameFlowMap_positive g o e he t)]
  exact congrArg FrameBundle.base (parallelFrameFlowMap_add g 0 s t e).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second derivative of the actual corrected-segment energy is its
normal Jacobi index plus intrinsic endpoint boundary terms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem normalSegmentSecond_integral (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (c : M) (N P : ℝ → Fin 3 → ℝ) {a b : ℝ} (hab : a < b)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b)) :
    (∫ t in a..b, chartEnergySecondDensity g c
      (chartAt FourSpace c (frameGeodesic g 0 e t))
      (normalChartField g c e N t) (geodesicChartVelocity g c e t)
      (normalChartFieldRate g c e N P t)
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t))
      (WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0))) =
      (∫ t in a..b, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (N t) (P t)) +
      normalEndpointBoundary g (parallelFrameFlowMap g 0 b e) (N b) -
      normalEndpointBoundary g (parallelFrameFlowMap g 0 a e) (N a) := by
  let U : ℝ → JacobiCoordinateVector := fun t =>
    WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 t)
  let Q : ℝ → JacobiCoordinateVector := fun _ =>
    WithLp.ofLp (endpointCorrectedMixedSecond A.second B.second a b 0)
  have hU : Continuous U := (PiLp.continuous_ofLp 2 _).comp
    ((continuous_endpointCorrectedSecond A.second B.second a b
      A.second_continuous B.second_continuous).comp (continuous_const.prodMk continuous_id))
  have hQ : Continuous Q := continuous_const
  have hu (t : ℝ) : HasDerivAt U (Q t) t :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).toContinuousLinearMap.hasFDerivAt
      |>.comp_hasDerivAt t (endpointCorrectedSecond_time A.second B.second a b 0 t)
  have hNc : ContinuousOn N (Icc a b) := fun t ht =>
    (hN t ht).continuousAt.continuousWithinAt
  have hS := continuousOn_chartEnergySecondDensity g c
    (fun t => chartAt FourSpace c (frameGeodesic g 0 e t))
    (normalChartField g c e N) (geodesicChartVelocity g c e)
    (normalChartFieldRate g c e N P) U Q
    (geodesicChartPosition_continuousOn g c e _ hc)
    (normalChartField_continuousOn g c e N _ hc hNc)
    (geodesicChartVelocity_continuousOn g c e _ hc)
    (normalChartFieldRate_continuousOn g c e N P _ hc hNc hP)
    hU.continuousOn hQ.continuousOn
    (fun t ht => (chartAt FourSpace c).map_source (hc t ht))
  have hi := normalChartField_second_integral g hRic c e N P U Q a b
    (by simpa only [uIcc_of_le hab.le, frameGeodesic] using hc)
    (by simpa only [uIcc_of_le hab.le] using hN)
    (by simpa only [uIcc_of_le hab.le] using hP)
    (fun t _ => hu t) (hS.intervalIntegrable_of_Icc hab.le)
  have hleft : chartEnergyBoundary g c (chartAt FourSpace c (frameGeodesic g 0 e a))
      (geodesicChartVelocity g c e a) (normalChartField g c e N a) (U a) =
      normalEndpointBoundary g (parallelFrameFlowMap g 0 a e) (N a) := by
    change chartEnergyBoundary g c _ _ _
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 a)) = _
    rw [endpointCorrectedSecond_left _ _ _ _ _ hab.ne, A.second_zero]
    exact normalEndpoint_boundary_chart g (parallelFrameFlowMap g 0 a e) c
      (hc a ⟨le_rfl, hab.le⟩) (N a)
  have hright : chartEnergyBoundary g c (chartAt FourSpace c (frameGeodesic g 0 e b))
      (geodesicChartVelocity g c e b) (normalChartField g c e N b) (U b) =
      normalEndpointBoundary g (parallelFrameFlowMap g 0 b e) (N b) := by
    change chartEnergyBoundary g c _ _ _
      (WithLp.ofLp (endpointCorrectedSecond A.second B.second a b 0 b)) = _
    rw [endpointCorrectedSecond_right _ _ _ _ _ hab.ne, B.second_zero]
    exact normalEndpoint_boundary_chart g (parallelFrameFlowMap g 0 b e) c
      (hc b ⟨hab.le, le_rfl⟩) (N b)
  simp only [frameGeodesic] at hleft hright
  rw [hleft, hright] at hi
  exact hi

theorem normalSegmentEnergy_index_secondDeriv (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (c : M) (N P : ℝ → Fin 3 → ℝ) {a b δ : ℝ}
    (hab : a < b) (hδ : 0 < δ)
    (hc : ∀ t ∈ Icc a b, frameGeodesic g 0 e t ∈ (chartAt FourSpace c).source)
    (hN : ∀ t ∈ Icc a b, HasDerivAt N (P t) t) (hP : ContinuousOn P (Icc a b))
    (A : NormalEndpointJetData g (parallelFrameFlowMap g 0 a e) c (N a))
    (B : NormalEndpointJetData g (parallelFrameFlowMap g 0 b e) c (N b))
    (hA : δ ≤ A.radius) (hB : δ ≤ B.radius)
    (hz : ∀ ε ∈ Icc (-δ) δ, ∀ t ∈ Icc a b,
      normalSegmentPosition g e c N A.position B.position a b ε t ∈ (chartAt FourSpace c).target) :
    HasDerivAt (deriv (normalSegmentEnergy g e c N P A.position B.position a b))
      ((∫ t in a..b, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) (N t) (P t)) +
        normalEndpointBoundary g (parallelFrameFlowMap g 0 b e) (N b) -
        normalEndpointBoundary g (parallelFrameFlowMap g 0 a e) (N a)) 0 := by
  have h := normalSegmentEnergy_secondDeriv g e c N P hab hδ hc hN hP A B hA hB hz
  rw [normalSegmentSecond_integral g hRic e c N P hab hc hN hP A B] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Nonnegativity of the normal index on a finite chart partition of an
actual minimizing geodesic.  The competitor curves and their endpoint jets
are constructed, rather than assumed as a second-variation input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem finite_geodesic_normal_index_nonneg (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (n : ℕ) (t : ℕ → ℝ) (c : ℕ → M)
    (N P : ℕ → ℝ → Fin 3 → ℝ)
    (ht : ∀ i < n, t i < t (i + 1))
    (hc : ∀ i < n, ∀ r ∈ Icc (t i) (t (i + 1)),
      frameGeodesic g 0 e r ∈ (chartAt FourSpace (c i)).source)
    (hN : ∀ i < n, ∀ r ∈ Icc (t i) (t (i + 1)), HasDerivAt (N i) (P i r) r)
    (hP : ∀ i < n, ContinuousOn (P i) (Icc (t i) (t (i + 1))))
    (hmatch : ∀ i < n, N i (t (i + 1)) = N (i + 1) (t (i + 1)))
    (hstart : N 0 (t 0) = 0) (hend : N n (t n) = 0)
    (hmin : metricDistance g (frameGeodesic g 0 e (t 0))
      (frameGeodesic g 0 e (t n)) = t n - t 0) :
    0 ≤ ∑ i ∈ Finset.range n, ∫ r in t i..t (i + 1),
      normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e))
        (N i r) (P i r) := by
  classical
  let A := fun i : Fin n => normalEndpointJetData g (parallelFrameFlowMap g 0 (t i.val) e)
    (c i.val) (hc i.val i.isLt (t i.val) ⟨le_rfl, (ht i.val i.isLt).le⟩) (N i.val (t i.val))
  let B := fun i : Fin n => normalEndpointJetData g (parallelFrameFlowMap g 0 (t (i.val + 1)) e)
    (c i.val) (hc i.val i.isLt (t (i.val + 1)) ⟨(ht i.val i.isLt).le, le_rfl⟩)
      (N i.val (t (i.val + 1)))
  have hNc (i : Fin n) : ContinuousOn (N i.val) (Icc (t i.val) (t (i.val + 1))) :=
    fun r hr => (hN i.val i.isLt r hr).continuousAt.continuousWithinAt
  choose δ hδ hδA hδB hinside using fun i : Fin n => normalSegment_common_radius g e (c i.val)
    (N i.val) (ht i.val i.isLt) (hc i.val i.isLt) (hNc i) (A i) (B i)
  let E : ℕ → ℝ → ℝ := fun i ε => if hi : i < n then
    normalSegmentEnergy g e (c i) (N i) (P i) (A ⟨i, hi⟩).position (B ⟨i, hi⟩).position
      (t i) (t (i + 1)) ε else 0
  let γ : ℕ → ℝ → ℝ → M := fun i ε => if hi : i < n then
    normalSegmentCurve g e (c i) (N i) (A ⟨i, hi⟩).position (B ⟨i, hi⟩).position
      (t i) (t (i + 1)) ε else frameGeodesic g 0 e
  let p : ℝ → ℕ → M := fun ε i =>
    normalEndpointCurve g (parallelFrameFlowMap g 0 (t i) e) (N i (t i)) ε
  let I : ℕ → ℝ := fun i => ∫ r in t i..t (i + 1),
    normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) (N i r) (P i r)
  let L : ℕ → ℝ := fun i => normalEndpointBoundary g (parallelFrameFlowMap g 0 (t i) e) (N i (t i))
  let R : ℕ → ℝ := fun i => normalEndpointBoundary g (parallelFrameFlowMap g 0 (t (i + 1)) e)
    (N i (t (i + 1)))
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin n, ε ∈ Icc (-δ i) (δ i) := by
    apply eventually_all.mpr
    intro i
    exact Icc_mem_nhds (neg_neg_of_pos (hδ i)) (hδ i)
  have hfd : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i < n, DifferentiableAt ℝ (E i) ε := by
    have hf : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : Fin n, DifferentiableAt ℝ (E i.val) ε := by
      apply eventually_all.mpr
      intro i
      simpa only [E, dite_eq_left i.isLt] using
        normalSegmentEnergy_first_differentiable g e (c i.val) (N i.val) (P i.val)
          (ht i.val i.isLt) (hδ i) (hc i.val i.isLt) (hN i.val i.isLt) (hP i.val i.isLt)
          (A i) (B i) (hδA i) (hδB i) (hinside i)
    filter_upwards [hf] with ε hε i hi
    exact hε ⟨i, hi⟩
  have hzero : (∑ i ∈ Finset.range n, E i 0) = (t n - t 0) / 2 := by
    calc
      _ = ∑ i ∈ Finset.range n, (t (i + 1) - t i) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        simpa only [E, dite_eq_left hi'] using
          normalSegmentEnergy_zero g e (c i) (N i) (P i) (ht i hi') (hc i hi')
            (hN i hi') (A ⟨i, hi'⟩) (B ⟨i, hi'⟩)
      _ = _ := by rw [← Finset.sum_div, Finset.sum_range_sub]
  have hlocal : IsLocalMin (fun ε => ∑ i ∈ Finset.range n, E i ε) 0 := by
    filter_upwards [hnear] with ε hε
    have hregion (i : ℕ) (hi : i < n) :
        ε ∈ Icc (-(A ⟨i, hi⟩).radius) (A ⟨i, hi⟩).radius ∧
        ε ∈ Icc (-(B ⟨i, hi⟩).radius) (B ⟨i, hi⟩).radius := by
      have h := hε ⟨i, hi⟩
      have hA := hδA ⟨i, hi⟩
      have hB := hδB ⟨i, hi⟩
      constructor <;> constructor <;> linarith [h.1, h.2]
    have hγ (i : ℕ) (hi : i < n) :
        ContMDiffOn 𝓘(ℝ, ℝ) I4 1 (γ i ε) (Icc (t i) (t (i + 1))) := by
      simpa only [γ, dite_eq_left hi] using normalSegmentCurve_contMDiffOn g e (c i)
        (N i) (P i) (A ⟨i, hi⟩).position (B ⟨i, hi⟩).position (ht i hi) (hc i hi)
        (hN i hi) (hP i hi) (hinside ⟨i, hi⟩ ε (hε ⟨i, hi⟩))
    have hends (i : ℕ) (hi : i < n) :
        γ i ε (t i) = p ε i ∧ γ i ε (t (i + 1)) = p ε (i + 1) := by
      have h := normalSegmentCurve_endpoints g e (c i) (N i) (ht i hi)
        (A ⟨i, hi⟩) (B ⟨i, hi⟩) (hregion i hi).1 (hregion i hi).2
      simpa only [γ, dite_eq_left hi, p, hmatch i hi] using h
    have hp0 : p ε 0 = frameGeodesic g 0 e (t 0) := by
      simpa only [p, hstart, frameGeodesic] using normalEndpointCurve_zero g (parallelFrameFlowMap g 0 (t 0) e) ε
    have hpn : p ε n = frameGeodesic g 0 e (t n) := by
      simpa only [p, hend, frameGeodesic] using normalEndpointCurve_zero g (parallelFrameFlowMap g 0 (t n) e) ε
    have hb := finite_piece_metric_energy_lower g n (p ε) t (fun i => γ i ε) ht hγ
      (fun i hi => (hends i hi).1) (fun i hi => (hends i hi).2)
    have heq : (∑ i ∈ Finset.range n, metricCurveEnergy g (γ i ε) (t i) (t (i + 1))) =
        ∑ i ∈ Finset.range n, E i ε := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' := Finset.mem_range.mp hi
      simpa only [γ, E, dite_eq_left hi'] using
        (normalSegmentEnergy_eq_actual g e (c i) (N i) (P i) (A ⟨i, hi'⟩).position
          (B ⟨i, hi'⟩).position (ht i hi') (hc i hi') (hN i hi')
          (hinside ⟨i, hi'⟩ ε (hε ⟨i, hi'⟩))).symm
    rw [hp0, hpn, hmin, heq] at hb
    rw [hzero]
    linarith
  apply finite_piece_index_nonneg n E I L R hlocal hfd
  · intro i hi
    simpa only [E, dite_eq_left hi, I, L, R] using
      normalSegmentEnergy_index_secondDeriv g hRic e (c i) (N i) (P i) (ht i hi) (hδ ⟨i, hi⟩)
        (hc i hi) (hN i hi) (hP i hi) (A ⟨i, hi⟩) (B ⟨i, hi⟩)
        (hδA ⟨i, hi⟩) (hδB ⟨i, hi⟩) (hinside ⟨i, hi⟩)
  · intro i hi
    exact congrArg (normalEndpointBoundary g (parallelFrameFlowMap g 0 (t (i + 1)) e)) (hmatch i hi)
  · simpa only [L, hstart] using normalEndpointBoundary_zero g (parallelFrameFlowMap g 0 (t 0) e)
  · simpa only [L, hend] using normalEndpointBoundary_zero g (parallelFrameFlowMap g 0 (t n) e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact set of minimizing tangent vectors and its polar
cut-time description. Its exponential image is the whole manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

omit [PreconnectedSpace M] in
theorem frameExponential_direction_ray (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (q : Directions) (r : ℝ) :
    frameExponential g o e (r • q.val) =
      frameGeodesic g 0 (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) r := by
  have hdir := directionRotation_first q
  have hp := frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  rw [← frameExponential_first_ray_all g o _ hp r, frameExponential_rotate, map_smul, hdir]

theorem actualMinimizingTangentDomain_ray_iff (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (he : e ∈ o.positive)
    (q : Directions) (r : ℝ) (hr : 0 ≤ r) :
    r • q.val ∈ actualMinimizingTangentDomain g o e ↔
      r ≤ actualCutTime g (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) := by
  let f := e.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  have hnorm : ‖r • q.val‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, q.property, mul_one]
  change metricDistance g e.base (frameExponential g o e (r • q.val)) = ‖r • q.val‖ ↔ _
  rw [hnorm, metricDistance_eq_iff g e.base _ hr, frameExponential_direction_ray g o e he q r]
  have htime : (r ∈ frameMinimizingTimes g f) ↔ r ≤ actualCutTime g f := by
    rw [frameMinimizingTimes_eq_Icc]
    exact and_iff_right hr
  exact (and_iff_right hr).symm.trans htime

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual index inequality for a continuous normal field with a single
corner.  Each of its two C1 branches is subdivided into genuine chart pieces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem two_piece_geodesic_index_nonneg (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) (a c b : ℝ) (hac : a < c) (hcb : c < b)
    (NL NR PL PR : ℝ → Fin 3 → ℝ)
    (hNL : ∀ r, HasDerivAt NL (PL r) r) (hNR : ∀ r, HasDerivAt NR (PR r) r)
    (hPL : Continuous PL) (hPR : Continuous PR)
    (hjoin : NL c = NR c) (hstart : NL a = 0) (hend : NR b = 0)
    (hmin : metricDistance g (frameGeodesic g 0 e a) (frameGeodesic g 0 e b) = b - a) :
    0 ≤ (∫ r in a..c, normalIndexDensity
      (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) (NL r) (PL r)) +
      ∫ r in c..b, normalIndexDensity
        (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) (NR r) (PR r) := by
  classical
  obtain ⟨n, hn, C, hC⟩ := exists_finite_curve_chart_partition (frameGeodesic g 0 e)
    (frameGeodesic_continuous g 0 e) a c hac
  obtain ⟨m, hm, D, hD⟩ := exists_finite_curve_chart_partition (frameGeodesic g 0 e)
    (frameGeodesic_continuous g 0 e) c b hcb
  let T := joinedPartitionTime a c b n m
  let charts := fun i => if i < n then C i else D (i - n)
  let N := fun i => if i < n then NL else NR
  let P := fun i => if i < n then PL else PR
  have hT0 : T 0 = a := joinedPartitionTime_zero a c b n m
  have hTn : T n = c := by
    change joinedPartitionTime a c b n m n = c
    rw [joinedPartitionTime_left _ _ _ _ _ _ le_rfl, affinePartitionTime_last _ _ _ hn]
  have hTend : T (n + m) = b := joinedPartitionTime_last a c b n m hn hm
  have hcharts := joinedPartition_chart_cover (frameGeodesic g 0 e) a c b n m hn C D hC hD
  have hindex : 0 ≤ ∑ i ∈ Finset.range (n + m), ∫ r in T i..T (i + 1),
      normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e))
        (N i r) (P i r) := by
    apply finite_geodesic_normal_index_nonneg g hRic e (n + m) T charts N P
    · intro i _
      exact joinedPartitionTime_step_lt a c b n m i hac hcb hn hm
    · exact hcharts
    · intro i _ r _
      dsimp only [N, P]
      split_ifs <;> first | exact hNL r | exact hNR r
    · intro i _
      dsimp only [P]
      split_ifs <;> first | exact hPL.continuousOn | exact hPR.continuousOn
    · intro i _
      by_cases hi : i < n
      · by_cases hnext : i + 1 < n
        · simp only [N, ite_eq_left hi, ite_eq_left hnext]
        · have hi' : i + 1 = n := by omega
          simp only [N, ite_eq_left hi, ite_eq_right hnext]
          rw [hi', hTn]
          exact hjoin
      · have hnext : ¬ i + 1 < n := by omega
        simp only [N, ite_eq_right hi, ite_eq_right hnext]
    · simpa only [N, ite_eq_left hn, hT0] using hstart
    · have hnot : ¬ n + m < n := by omega
      simpa only [N, ite_eq_right hnot, hTend] using hend
    · simpa only [hT0, hTend] using hmin
  let F := fun r => normalIndexDensity
    (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) (NL r) (PL r)
  let G := fun r => normalIndexDensity
    (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) (NR r) (PR r)
  have hR : Continuous (fun r => 1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e)) :=
    actualJacobiCurvature_continuous g hRic e
  have hF : Continuous F := continuous_normalIndexDensity hR
    (continuous_iff_continuousAt.mpr fun r => (hNL r).continuousAt) hPL
  have hG : Continuous G := continuous_normalIndexDensity hR
    (continuous_iff_continuousAt.mpr fun r => (hNR r).continuousAt) hPR
  have heq : (∑ i ∈ Finset.range (n + m), ∫ r in T i..T (i + 1),
      normalIndexDensity (1 + frameCurvatureField g (parallelFrameFlowMap g 0 r e))
        (N i r) (P i r)) =
      ∑ i ∈ Finset.range (n + m), ∫ r in T i..T (i + 1), if i < n then F r else G r := by
    apply Finset.sum_congr rfl
    intro i _
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only [N, P, F, G]
    split_ifs <;> rfl
  rw [heq, joinedPartition_sum_integral a c b n m hn hm F G hF hG] at hindex
  exact hindex

end
end PositiveEinsteinFour.Geometry
end


section

/-! A minimizing geodesic cannot continue beyond its first conjugate point.
The negative Jacobi test field contradicts the index inequality obtained
from actual, endpoint-compatible variations of the minimizing segment. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Jacobi Matrix MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]

theorem actualCutTime_le_firstConjugateTime (g : SmoothMetric M)
    (hRic : RicciThree g) (e : FrameBundle g) :
    actualCutTime g e ≤ actualFirstConjugateTime g hRic e := by
  by_contra hnot
  have hcb : actualFirstConjugateTime g hRic e < actualCutTime g e :=
    lt_of_not_ge hnot
  let d := actualJacobiSolution g hRic e
  let c := actualFirstConjugateTime g hRic e
  let b := actualCutTime g e
  have hc : 0 < c := actualFirstConjugateTime_pos g hRic e
  obtain ⟨w, _, hJ, hV⟩ := exists_actualFirstConjugate_vector g hRic e
  obtain ⟨ε, _, hneg⟩ := d.exists_negative_conjugate_index
    (actualJacobiCurvature_continuous g hRic e)
    (actualJacobiCurvature_symmetric g e) w hc hcb hJ hV
  have hmin : metricDistance g (frameGeodesic g 0 e 0)
      (frameGeodesic g 0 e b) = b - 0 := by
    have hb := actualCutTime_mem g e
    have hzero : frameGeodesic g 0 e 0 = e.base := by
      simp only [frameGeodesic, parallelFrameFlowMap_zero]
    rw [hzero, sub_zero]
    exact (metricDistance_eq_iff g e.base (frameGeodesic g 0 e b) hb.1).mpr hb.2
  have hind := two_piece_geodesic_index_nonneg g hRic e 0 c b hc hcb
    (conjugateLeftField d w c b ε) (conjugateRightField d w c b ε)
    (conjugateLeftRate d w c b ε) (conjugateRightRate d w c b ε)
    (conjugateLeftField_hasDerivAt d w c b ε)
    (conjugateRightField_hasDerivAt d w c b ε)
    (conjugateLeftRate_continuous d w c b ε)
    (conjugateRightRate_continuous d w c b ε)
    (conjugateBranches_agree d w c b ε hJ)
    (conjugateBranches_endpoints d w c b ε).1
    (conjugateBranches_endpoints d w c b ε).2 hmin
  change 0 ≤ conjugateIndexAction d w c b ε at hind
  exact (not_le_of_gt hneg) hind

theorem actualCutTime_le_pi (g : SmoothMetric M) (hRic : RicciThree g)
    (e : FrameBundle g) : actualCutTime g e ≤ Real.pi :=
  (actualCutTime_le_firstConjugateTime g hRic e).trans
    (actualFirstConjugateTime_le_pi g hRic e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric Jacobian formula in every initial direction. An oriented
rotation of the initial frame contributes determinant one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_chart_det_rotate (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (Q : OrientedOrthogonalFour) (d : M) (v : FourSpace)
    (hd : frameExponential g o e
      (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
        (orientedToOrthogonal Q).property v) ∈ (chartAt FourSpace d).source) :
    LinearMap.det (fderiv ℝ (fun w => chartAt FourSpace d
      (frameExponential g o (e.rotate (orientedToOrthogonal Q)) w)) v).toLinearMap =
    LinearMap.det (fderiv ℝ (fun w => chartAt FourSpace d (frameExponential g o e w))
      (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
        (orientedToOrthogonal Q).property v)).toLinearMap := by
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
    (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  let F := fun w => chartAt FourSpace d (frameExponential g o e w)
  have hF : DifferentiableAt ℝ F (L v) :=
    (frameExponential_chart_contDiffAt g o d e (L v) hd).differentiableAt (by first | simp | exact_mod_cast le_top)
  have hL : HasFDerivAt (fun w => L w) (L : FourSpace →L[ℝ] FourSpace) v :=
    (L : FourSpace →L[ℝ] FourSpace).hasFDerivAt
  have h := hF.hasFDerivAt.comp v hL
  have heq : (fun w => F (L w)) = (fun w => chartAt FourSpace d
      (frameExponential g o (e.rotate (orientedToOrthogonal Q)) w)) := by
    funext w
    exact congrArg (chartAt FourSpace d) (frameExponential_rotate g o e Q w).symm
  change HasFDerivAt (fun w => F (L w)) ((fderiv ℝ F (L v)).comp
    (L : FourSpace →L[ℝ] FourSpace)) v at h
  rw [heq] at h
  rw [h.fderiv]
  change LinearMap.det ((fderiv ℝ F (L v)).toLinearMap.comp L.toLinearEquiv.toLinearMap) = _
  rw [LinearMap.det_comp]
  have hdet : LinearMap.det L.toLinearEquiv.toLinearMap = 1 := orientedEuclidean_det Q
  rw [hdet, mul_one]
  rfl

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The L² translation bound as a scalar oscillation integral, averaged over
the actual spherical directions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff BigOperators ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarOscillation_compact
theorem scalarGeodesicOscillation_integral_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a : SmoothScalar (M := M)) (t : ℝ) :
    (∫⁻ e, scalarGeodesicOscillation g a t e ∂canonicalFrameMeasure g o) ≤
      ENNReal.ofReal (t ^ 2 *
        ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) 0 a‖ ^ 2) := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hz : ∀ e, ((canonicalParallelMetricData g o hRic).flow 0).map 0 e = e :=
    fun e => actualParallelMetricData_zero g (canonicalFrameMeasure g o)
      (parallelFrameFlowMap_measurePreserving g o) hRic 0 e
  simpa only [scalarGeodesicOscillation] using!
    smoothScalar_flow_oscillation_bound (canonicalParallelMetricData g o hRic) 0 hz a t

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrating the flow translation estimate over the bounded
radial interval gives a global pair-oscillation energy estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarPairEnergy_compact
theorem scalar_radial_lintegral_energy_bound (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a : SmoothScalar (M := M)) :
    (∫⁻ r in Icc (0 : ℝ) Real.pi, ∫⁻ e,
      scalarGeodesicOscillation g a r e ∂canonicalFrameMeasure g o) ≤
      ENNReal.ofReal (Real.pi ^ 3 *
        ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) 0 a‖ ^ 2) := by
  let A := ‖smoothScalarGradientL2 (canonicalParallelMetricData g o hRic) 0 a‖ ^ 2
  have hpoint (r : ℝ) (hr : r ∈ Icc (0 : ℝ) Real.pi) :
      (∫⁻ e, scalarGeodesicOscillation g a r e ∂canonicalFrameMeasure g o) ≤
        ENNReal.ofReal (Real.pi ^ 2 * A) := by
    refine (scalarGeodesicOscillation_integral_bound g o hRic a r).trans ?_
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ hr.1 Real.pi_pos.le).mpr hr.2) (sq_nonneg _)
  calc
    _ ≤ ∫⁻ _r in Icc (0 : ℝ) Real.pi, ENNReal.ofReal (Real.pi ^ 2 * A) :=
      lintegral_mono_ae ((ae_restrict_mem measurableSet_Icc).mono hpoint)
    _ = _ := by
      rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
        ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      congr 1
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Unconditional weak Poisson solvability for the actual metric.  The
Poincaré constant comes from the exponential-map pair estimate.  The value
of the solution is a scalar on the base manifold, and its equation holds
against every element of the actual first-jet completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

section General

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {μ : Measure (FrameBundle g)}
  [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

/-- A mean-zero source pairs identically with a test and its mean-zero
projection.  Consequently the variational solution tests against all H¹. -/
theorem scalarMeanZeroWeakPoisson_all_tests (d : ParallelMetricData g μ)
    {K : ℝ} (hK : 0 < K) (hP : SmoothScalarPoincare d K)
    (f : ScalarL2 g μ) (hf : inner ℝ f (scalarL2One g μ) = 0)
    (v : scalarH1 d) :
    (∑ i : Fin 4, inner ℝ
      (scalarH1Gradient d i (scalarMeanZeroWeakPoisson d hK hP f).val)
      (scalarH1Gradient d i v)) = inner ℝ f (scalarH1Value d v) := by
  have h := scalarMeanZeroWeakPoisson_weak d hK hP f
    (scalarH1MeanZeroProjection d v)
  change (∑ i : Fin 4, inner ℝ
    (scalarH1Gradient d i (scalarMeanZeroWeakPoisson d hK hP f).val)
    (scalarH1Gradient d i (scalarH1SubtractMean d v))) =
      inner ℝ f (scalarH1Value d (scalarH1SubtractMean d v)) at h
  simpa only [scalarH1Gradient_subtractMean, scalarH1Value_subtractMean,
    inner_sub_right, inner_smul_right, hf, mul_zero, sub_zero] using h

end General

end
end PositiveEinsteinFour.Geometry
end


section

/-! A smooth representative of a weak scalar Poisson solution satisfies the
pointwise geometric Poisson equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarStrong_compact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarStrong_probability
theorem smoothScalarValueL2_injective (g : SmoothMetric M) (o : FrameOrientation g) :
    Function.Injective (smoothScalarValueL2 g (canonicalFrameMeasure g o)) := by
  let := normalizedVolume_isOpenPosMeasure g
  intro a b hab
  have hbase : smoothScalarBaseL2 g a = smoothScalarBaseL2 g b := by
    apply (scalarBasePullback g o).injective
    simpa only [scalarBasePullback_smooth] using hab
  have hc := (ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) (normalizedVolume g)) hbase
  apply Subtype.ext
  exact congrArg DFunLike.coe hc

/-- A smooth representative of the constructed weak solution satisfies the
actual pointwise geometric Poisson equation. -/
theorem scalar_poisson_pointwise_of_smooth_representative (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (a φ : SmoothScalar (M := M))
    (u : scalarH1 (canonicalParallelMetricData g o hRic))
    (hu : scalarH1Value (canonicalParallelMetricData g o hRic) u =
      smoothScalarValueL2 g (canonicalFrameMeasure g o) φ)
    (hweak : ∀ v : scalarH1 (canonicalParallelMetricData g o hRic),
      (∑ i : Fin 4, inner ℝ
        (scalarH1Gradient (canonicalParallelMetricData g o hRic) i u)
        (scalarH1Gradient (canonicalParallelMetricData g o hRic) i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o)
          (smoothScalarSubtractMean (μ := canonicalFrameMeasure g o) a))
          (scalarH1Value (canonicalParallelMetricData g o hRic) v))) :
    ∀ e : FrameBundle g, scalarLaplacian g φ e =
      a.val e.base - ∫ f, a.val f.base ∂canonicalFrameMeasure g o := by
  let d := canonicalParallelMetricData g o hRic
  let μ := canonicalFrameMeasure g o
  let c := smoothScalarSubtractMean (μ := μ) a
  have hueq : u = smoothScalarToH1 d φ := scalarH1_eq_smooth_of_value d u φ hu
  have ht (b : SmoothScalar (M := M)) :
      inner ℝ (smoothScalarLaplacianL2 (μ := μ) φ - smoothScalarValueL2 g μ c)
        (smoothScalarValueL2 g μ b) = 0 := by
    have hw := hweak (smoothScalarToH1 d b)
    rw [hueq] at hw
    change smoothScalarDirichlet d φ b =
      -(inner ℝ (smoothScalarValueL2 g μ c) (smoothScalarValueL2 g μ b)) at hw
    rw [smoothScalarDirichlet_symm, smoothScalarDirichlet_laplacian_pairing,
      real_inner_comm (smoothScalarLaplacianL2 (μ := μ) φ) (smoothScalarValueL2 g μ b)] at hw
    rw [inner_sub_left]
    linarith
  let r := smoothScalarLaplacian g φ - c
  have hr : smoothScalarValueL2 g μ r =
      smoothScalarLaplacianL2 (μ := μ) φ - smoothScalarValueL2 g μ c := by
    dsimp only [r]
    rw [map_sub, smoothScalarLaplacian_valueL2]
  have hz : smoothScalarValueL2 g μ r = 0 := by
    have h := ht r
    rw [← hr] at h
    exact (inner_self_eq_zero).mp h
  have hr0 : r = 0 := smoothScalarValueL2_injective g o (by simpa only [map_zero] using hz)
  intro e
  have h := congrArg (fun b : SmoothScalar (M := M) => b.val e.base) hr0
  change scalarLaplacianBase g φ e.base -
    (a.val e.base - (∫ f, a.val f.base ∂μ) * 1) = 0 at h
  rw [scalarLaplacian_eq_base]
  dsimp only [μ] at h
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The distributional Poisson equation in metric chart measure.
Its coordinate density is derived from Riemannian volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function Filter
open scoped Manifold ContDiff ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

section Compact

variable [CompactSpace M] [Nonempty M] [SecondCountableTopology M]
  [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarChartIntegral_probability
omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem smoothScalarBaseL2_inner_right (g : SmoothMetric M)
    (b : Lp ℝ 2 (normalizedVolume g)) (v : SmoothScalar (M := M)) :
    inner ℝ b (smoothScalarBaseL2 g v) = ∫ x, b x * v.val x ∂normalizedVolume g := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
    (⟨v.val, v.property.continuous⟩ : C(M, ℝ))] with x hx
  simp only [smoothScalarBaseL2] at *
  rw [hx, real_inner_comm]
  rfl

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem smoothScalarBaseL2_inner (g : SmoothMetric M)
    (u v : SmoothScalar (M := M)) :
    inner ℝ (smoothScalarBaseL2 g u) (smoothScalarBaseL2 g v) =
      ∫ x, u.val x * v.val x ∂normalizedVolume g := by
  rw [smoothScalarBaseL2_inner_right]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
    (⟨u.val, u.property.continuous⟩ : C(M, ℝ))] with x hx
  rw [show smoothScalarBaseL2 g u x = u.val x from hx]

end Compact
end
end PositiveEinsteinFour.Geometry
end


section

/-! Base L² scalars are locally Euclidean L² in every metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

theorem scalarChartL2_weighted (g : SmoothMetric M) (c : M)
    (b : Lp ℝ 2 (normalizedVolume g)) :
    MemLp (fun z : ChartTarget c => b ((chartAt FourSpace c).symm z.val)) 2
      ((chartCoordinateMeasure c).withDensity
        (fun z => ENNReal.ofReal (chartVolumeDensity g c z))) := by
  have hb := (Lp.memLp b).restrict (chartAt FourSpace c).source
  rw [normalizedVolume_restrict_chart] at hb
  obtain ⟨hF₀, hFtop⟩ := ENNReal.toReal_pos_iff.mp (normalizedChartFactor_toReal_pos g)
  have hb' := hb.smul_measure (c := (normalizedChartFactor g)⁻¹)
    (ENNReal.inv_ne_top.mpr hF₀.ne')
  rw [smul_smul, ENNReal.inv_mul_cancel hF₀.ne' hFtop.ne, one_smul] at hb'
  have he : MeasurableEmbedding
      (fun z : ChartTarget c => (chartAt FourSpace c).symm z.val) :=
    (chartAt FourSpace c).symm.isOpenEmbedding_restrict.measurableEmbedding
  exact he.memLp_map_measure_iff.mp hb'

theorem scalarChartL2_compact (g : SmoothMetric M) (c : M)
    (b : Lp ℝ 2 (normalizedVolume g)) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target) :
    MemLp (fun z : FourSpace => b ((chartAt FourSpace c).symm z)) 2
      (volume.restrict K) := by
  let μ := chartCoordinateMeasure c
  let ρ : ChartTarget c → ℝ≥0∞ := fun z => ENNReal.ofReal (chartVolumeDensity g c z)
  let S : Set (ChartTarget c) := Subtype.val ⁻¹' K
  have hS : MeasurableSet S := measurable_subtype_coe hK.isClosed.measurableSet
  obtain ⟨δ, hδ, hδK⟩ := scalarChart_density_lower_bound g c hK hKt
  let d := ENNReal.ofReal δ
  have hd₀ : d ≠ 0 := (ENNReal.ofReal_pos.mpr hδ).ne'
  have hdtop : d ≠ (∞ : ℝ≥0∞) := ENNReal.ofReal_ne_top
  have hmeasure : d • μ.restrict S ≤ (μ.withDensity ρ).restrict S := by
    rw [← withDensity_const, restrict_withDensity hS]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hS] with z hz
    exact ENNReal.ofReal_le_ofReal (hδK z.val hz)
  have hdom : μ.restrict S ≤ d⁻¹ • μ.withDensity ρ := by
    calc
      μ.restrict S = d⁻¹ • (d • μ.restrict S) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hd₀ hdtop, one_smul]
      _ ≤ d⁻¹ • (μ.withDensity ρ).restrict S := smul_le_smul_left _ hmeasure
      _ ≤ d⁻¹ • μ.withDensity ρ := by
        gcongr
        exact Measure.restrict_le_self
  have hb : MemLp (fun z : ChartTarget c => b ((chartAt FourSpace c).symm z.val)) 2
      (μ.restrict S) :=
    (scalarChartL2_weighted g c b).of_measure_le_smul (ENNReal.inv_ne_top.mpr hd₀) hdom
  have he := MeasurableEmbedding.subtype_coe (chartAt FourSpace c).open_target.measurableSet
  have hmap : Measure.map (Subtype.val : ChartTarget c → FourSpace) (μ.restrict S) =
      volume.restrict K := by
    rw [← he.restrict_map]
    change (Measure.map Subtype.val (Measure.comap Subtype.val volume)).restrict K = _
    rw [map_comap_subtype_coe (chartAt FourSpace c).open_target.measurableSet,
      Measure.restrict_restrict hK.isClosed.measurableSet,
      inter_eq_left.mpr hKt]
  rw [← hmap]
  exact he.memLp_map_measure_iff.mpr hb

theorem scalarChartL2_cutoff (g : SmoothMetric M) (c : M)
    (b : Lp ℝ 2 (normalizedVolume g)) (χ : FourSpace → ℝ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (chartAt FourSpace c).target) :
    MemLp (fun z : FourSpace => χ z * b ((chartAt FourSpace c).symm z)) 2 volume := by
  have hb := scalarChartL2_compact g c b hc hs
  obtain ⟨C, hC⟩ := (hc.isCompact_range hχ).isBounded.exists_norm_le
  have hprod : MemLp (fun z : FourSpace => χ z * b ((chartAt FourSpace c).symm z)) 2
      (volume.restrict (tsupport χ)) := by
    apply hb.of_le_mul (c := C) (hχ.aestronglyMeasurable.mul hb.aestronglyMeasurable)
    filter_upwards with z
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC (χ z) (mem_range_self z)) (norm_nonneg _)
  have heq : (tsupport χ).indicator
      (fun z : FourSpace => χ z * b ((chartAt FourSpace c).symm z)) =
      (fun z : FourSpace => χ z * b ((chartAt FourSpace c).symm z)) := by
    apply indicator_eq_self.2
    intro z hz
    exact (subset_tsupport χ) (left_ne_zero_of_mul hz)
  rw [← heq]
  exact (memLp_indicator_iff_restrict (isClosed_tsupport χ).measurableSet).mpr hprod

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate test equation for the actual second-order elliptic operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalarChartTest_laplacian [T2Space M] (g : SmoothMetric M)
    (c : M) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (chartAt FourSpace c).target)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    scalarLaplacianBase g (scalarChartLift c ψ) ((chartAt FourSpace c).symm z) =
      scalarChartOperator g c ψ z := by
  rw [← chartScalarLaplacian_eq_base g (scalarChartLift_smooth c ψ hψ hc hs) c ⟨z, hz⟩,
    chartScalarLaplacian_coefficients g _ c z hz]
  change scalarChartOperator g c
    (fun w => scalarChartLift c ψ ((chartAt FourSpace c).symm w)) z = _
  apply scalarChartOperator_congr_nhds
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact scalarChartLift_symm c ψ hw

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate equation for the same H¹ solution supplied by the
variational solver. This keeps its weak coordinate derivatives and its
distributional Poisson equation attached to one representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.h1Equation_frameCompact
local instance h1Equation_probability_r242dcf_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalarH1_weak_base_distribution (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : SmoothScalar (M := M)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
          (scalarH1Value d v))) (v : SmoothScalar (M := M)) :
    inner ℝ (scalarH1BaseValue g o d u) (smoothScalarBaseL2 g (smoothScalarLaplacian g v)) =
      inner ℝ (smoothScalarBaseL2 g f) (smoothScalarBaseL2 g v) := by
  have h := hw (smoothScalarToH1 d v)
  change (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u)
    (smoothScalarGradientL2 d i v)) =
      -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
        (smoothScalarValueL2 g (canonicalFrameMeasure g o) v)) at h
  have hg := scalarH1_green d u v
  have he : inner ℝ (scalarH1Value d u)
      (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) v) =
      inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
        (smoothScalarValueL2 g (canonicalFrameMeasure g o) v) := by linarith
  calc
    _ = inner ℝ (scalarBasePullback g o (scalarH1BaseValue g o d u))
        (scalarBasePullback g o (smoothScalarBaseL2 g (smoothScalarLaplacian g v))) :=
      ((scalarBasePullback g o).inner_map_map _ _).symm
    _ = inner ℝ (scalarH1Value d u)
        (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) v) := by
      rw [scalarH1BaseValue_spec, scalarBasePullback_smooth, smoothScalarLaplacian_valueL2]
    _ = _ := by
      rw [he, ← scalarBasePullback_smooth g o f, ← scalarBasePullback_smooth g o v,
        (scalarBasePullback g o).inner_map_map]

theorem scalarH1_weak_coordinate_distribution (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : SmoothScalar (M := M)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
          (scalarH1Value d v)))
    (c : M) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) :
    (∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
      (scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z) *
        scalarChartOperator g c ψ z)) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (f.val ((chartAt FourSpace c).symm z) * ψ z) := by
  let b := scalarH1BaseValue g o d u
  have h := scalarH1_weak_base_distribution g o d f u hw (scalarChartTest c ψ hψ hc hs)
  rw [smoothScalarBaseL2_inner_right, smoothScalarBaseL2_inner] at h
  have hsupport := scalarChartLift_tsupport c ψ hc hs
  have hleft : ∀ x, x ∉ (chartAt FourSpace c).source →
      b x * scalarLaplacianBase g (scalarChartLift c ψ) x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsupport (scalarLaplacianBase_tsupport g _ ht))), mul_zero]
  have hright : ∀ x, x ∉ (chartAt FourSpace c).source →
      f.val x * scalarChartLift c ψ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsupport ht)), mul_zero]
  change (∫ x, b x * scalarLaplacianBase g (scalarChartLift c ψ) x ∂normalizedVolume g) =
    ∫ x, f.val x * scalarChartLift c ψ x ∂normalizedVolume g at h
  rw [normalizedVolume_integral_chart g c _ hleft,
    normalizedVolume_integral_chart g c _ hright] at h
  apply (mul_left_cancel₀ (normalizedChartFactor_toReal_pos g).ne') at h
  calc
    _ = ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (b ((chartAt FourSpace c).symm z) *
          scalarLaplacianBase g (scalarChartLift c ψ) ((chartAt FourSpace c).symm z)) := by
      apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
      intro z hz
      dsimp only
      rw [scalarChartTest_laplacian g c ψ hψ hc hs z hz]
    _ = _ := h
    _ = _ := by
      apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
      intro z hz
      dsimp only
      rw [scalarChartLift_symm c ψ hz]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate equation with an actual L2 source for the H1 solution supplied by the
variational solver. This keeps its weak coordinate derivatives and its
distributional Poisson equation attached to one representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.h1EquationL2_frameCompact
local instance h1EquationL2_probability_r242dcf_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem scalarH1_L2_weak_base_distribution (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : Lp ℝ 2 (normalizedVolume g)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarBasePullback g o f)
          (scalarH1Value d v))) (v : SmoothScalar (M := M)) :
    inner ℝ (scalarH1BaseValue g o d u) (smoothScalarBaseL2 g (smoothScalarLaplacian g v)) =
      inner ℝ f (smoothScalarBaseL2 g v) := by
  have h := hw (smoothScalarToH1 d v)
  change (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u)
    (smoothScalarGradientL2 d i v)) =
      -(inner ℝ (scalarBasePullback g o f)
        (smoothScalarValueL2 g (canonicalFrameMeasure g o) v)) at h
  have hg := scalarH1_green d u v
  have he : inner ℝ (scalarH1Value d u)
      (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) v) =
      inner ℝ (scalarBasePullback g o f)
        (smoothScalarValueL2 g (canonicalFrameMeasure g o) v) := by linarith
  calc
    _ = inner ℝ (scalarBasePullback g o (scalarH1BaseValue g o d u))
        (scalarBasePullback g o (smoothScalarBaseL2 g (smoothScalarLaplacian g v))) :=
      ((scalarBasePullback g o).inner_map_map _ _).symm
    _ = inner ℝ (scalarH1Value d u)
        (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) v) := by
      rw [scalarH1BaseValue_spec, scalarBasePullback_smooth, smoothScalarLaplacian_valueL2]
    _ = _ := by
      rw [he, ← scalarBasePullback_smooth g o v,
        (scalarBasePullback g o).inner_map_map]

theorem scalarH1_L2_weak_coordinate_distribution (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : Lp ℝ 2 (normalizedVolume g)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarBasePullback g o f)
          (scalarH1Value d v)))
    (c : M) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ (chartAt FourSpace c).target) :
    (∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
      (scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z) *
        scalarChartOperator g c ψ z)) =
      ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (f ((chartAt FourSpace c).symm z) * ψ z) := by
  let b := scalarH1BaseValue g o d u
  have h := scalarH1_L2_weak_base_distribution g o d f u hw (scalarChartTest c ψ hψ hc hs)
  rw [smoothScalarBaseL2_inner_right, smoothScalarBaseL2_inner_right] at h
  have hsupport := scalarChartLift_tsupport c ψ hc hs
  have hleft : ∀ x, x ∉ (chartAt FourSpace c).source →
      b x * scalarLaplacianBase g (scalarChartLift c ψ) x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport
      (fun ht => hx (hsupport (scalarLaplacianBase_tsupport g _ ht))), mul_zero]
  have hright : ∀ x, x ∉ (chartAt FourSpace c).source →
      f x * scalarChartLift c ψ x = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsupport ht)), mul_zero]
  change (∫ x, b x * scalarLaplacianBase g (scalarChartLift c ψ) x ∂normalizedVolume g) =
    ∫ x, f x * scalarChartLift c ψ x ∂normalizedVolume g at h
  rw [normalizedVolume_integral_chart g c _ hleft,
    normalizedVolume_integral_chart g c _ hright] at h
  apply (mul_left_cancel₀ (normalizedChartFactor_toReal_pos g).ne') at h
  calc
    _ = ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (b ((chartAt FourSpace c).symm z) *
          scalarLaplacianBase g (scalarChartLift c ψ) ((chartAt FourSpace c).symm z)) := by
      apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
      intro z hz
      dsimp only
      rw [scalarChartTest_laplacian g c ψ hψ hc hs z hz]
    _ = _ := h
    _ = _ := by
      apply setIntegral_congr_fun (chartAt FourSpace c).open_target.measurableSet
      intro z hz
      dsimp only
      rw [scalarChartLift_symm c ψ hz]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic energy controls the local coordinate L² differential.
These estimates are uniform over the smooth scalars generating H¹. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartEnergy_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartEnergy_baseProbability
theorem scalarEnergyRootL2_norm_sq (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (a : SmoothScalar (M := M)) :
    ‖scalarEnergyRootL2 g a‖ ^ 2 = smoothScalarDirichlet d a a := by
  rw [← real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (scalarEnergyRoot g a))
    (ContinuousMap.toLp 2 (normalizedVolume g) ℝ (scalarEnergyRoot g a)) = _
  rw [ContinuousMap.inner_toLp]
  simp only [conj_trivial]
  have hs : (∫ x, (scalarEnergyRoot g a) x * (scalarEnergyRoot g a) x
      ∂normalizedVolume g) = ∫ x, scalarDirichletDensity g a x ∂normalizedVolume g := by
    apply integral_congr_ae
    filter_upwards with x
    change Real.sqrt (scalarDirichletDensity g a x) *
      Real.sqrt (scalarDirichletDensity g a x) = _
    rw [← pow_two, Real.sq_sqrt (scalarDirichletDensity_nonneg g a x)]
  rw [hs, smoothScalarDirichlet_eq_integral]
  rw [← (canonicalFrameMeasure_base g o).map_eq,
    integral_map (canonicalFrameMeasure_base g o).measurable.aemeasurable
      (by simpa only [(canonicalFrameMeasure_base g o).map_eq] using
        (scalarDirichletDensity_continuous g a.property).aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards with e
  rw [scalarDirichletDensity_eq_frame]
  simp only [pow_two]

theorem scalarEnergyRootL2_norm_le (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (a : SmoothScalar (M := M)) :
    ‖scalarEnergyRootL2 g a‖ ≤ ‖smoothScalarToH1 d a‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [scalarEnergyRootL2_norm_sq g o d, scalarH1_norm_sq]
  simp only [scalarH1Value_smooth, scalarH1Gradient_smooth, smoothScalarDirichlet,
    real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate differential extends continuously from smooth scalars
to the actual intrinsic H¹ completion on every compact chart set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartH1_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartH1_baseProbability
def smoothScalarH1Map {g : SmoothMetric M} (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    SmoothScalar (M := M) →ₗ[ℝ] scalarH1 d where
  toFun := smoothScalarToH1 d
  map_add' a b := Subtype.ext ((smoothScalarFirstJet d).map_add a b)
  map_smul' r a := Subtype.ext ((smoothScalarFirstJet d).map_smul r a)

theorem smoothScalarH1Map_dense {g : SmoothMetric M} (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) : DenseRange (smoothScalarH1Map o d) := by
  change Dense (range (smoothScalarH1Map o d))
  rw [Topology.IsInducing.subtypeVal.dense_iff]
  intro u
  apply closure_mono (s := range (smoothScalarFirstJet d)) ?_ u.property
  rintro v ⟨a, rfl⟩
  exact ⟨smoothScalarToH1 d a, ⟨a, rfl⟩, rfl⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Multiplying a local L² representative by a compact cutoff gives a
genuine global L² function, independent of its values off the local set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

theorem scalarLocalL2Product_integral {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) (ψ : FourSpace → ℝ) :
    (∫ z, scalarLocalL2Product hK χ hχ hc hs f z * ψ z) =
      ∫ z in K, χ z * f z * ψ z := by
  have he := integral_congr_ae ((scalarLocalL2Product_coe hK χ hχ hc hs f).mul
    (Filter.EventuallyEq.rfl (f := ψ)))
  simp only [Pi.mul_apply] at he
  rw [he]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (hs ht)), zero_mul, zero_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local H¹ derivatives give genuine global weak derivatives after a
compact cutoff. No differentiability of an L² representative is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

def scalarLocalL2PartialProduct {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) (i : Fin 4) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  scalarLocalL2Product hK (fun w => partialDeriv χ i w)
    (((hχ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := coordinateVector i))).continuous)
    (hc.fderiv_apply ℝ (coordinateVector i))
    ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs) f

theorem scalarLocalL2PartialProduct_integral {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f : Lp ℝ 2 (volume.restrict K)) (i : Fin 4)
    (ψ : FourSpace → ℝ) :
    (∫ z, scalarLocalL2PartialProduct hK χ hχ hc hs f i z * ψ z) =
      ∫ z in K, partialDeriv χ i z * f z * ψ z :=
  scalarLocalL2Product_integral ..

theorem scalarLocalL2_weak_product {K : Set FourSpace} (hK : MeasurableSet K)
    (f g : Lp ℝ 2 (volume.restrict K)) (i : Fin 4)
    (hw : ∀ (q : FourSpace → ℝ), ContDiff ℝ ∞ q → HasCompactSupport q →
      tsupport q ⊆ K → (∫ z in K, f z * partialDeriv q i z) =
        -(∫ z in K, g z * q z))
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    (∫ z, scalarLocalL2Product hK χ hχ.continuous hc hs f z * partialDeriv ψ i z) =
      -((∫ z, scalarLocalL2Product hK χ hχ.continuous hc hs g z * ψ z) +
        ∫ z, scalarLocalL2PartialProduct hK χ hχ hc hs f i z * ψ z) := by
  have hDχ : ContDiff ℝ ∞ (fun w => partialDeriv χ i w) :=
    (hχ.fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply
      (contDiff_const (c := coordinateVector i))
  have hDψ : ContDiff ℝ ∞ (fun w => partialDeriv ψ i w) :=
    (hψ.fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply
      (contDiff_const (c := coordinateVector i))
  have hint₁ := scalarLocalL2_mul_integrable f
    (fun z => partialDeriv χ i z * ψ z) (hDχ.continuous.mul hψ.continuous)
    ((hc.fderiv_apply ℝ (coordinateVector i)).mul_right)
  have hint₂ := scalarLocalL2_mul_integrable f
    (fun z => χ z * partialDeriv ψ i z) (hχ.continuous.mul hDψ.continuous) hc.mul_right
  have hweak := hw (fun z => χ z * ψ z) (hχ.mul hψ) hc.mul_right
    (tsupport_mul_subset_left.trans hs)
  have hexpand : (∫ z in K, f z * partialDeriv (fun w => χ w * ψ w) i z) =
      (∫ z in K, f z * (partialDeriv χ i z * ψ z)) +
        ∫ z in K, f z * (χ z * partialDeriv ψ i z) := by
    rw [← integral_add hint₁ hint₂]
    apply integral_congr_ae
    filter_upwards with z
    rw [scalar_partial_product χ ψ z (hχ.differentiable (by simp) z)
      (hψ.differentiable (by simp) z)]
    ring
  rw [hexpand] at hweak
  simp only [scalarLocalL2Product_integral, scalarLocalL2PartialProduct_integral]
  have he₁ : (∫ z in K, f z * (χ z * partialDeriv ψ i z)) =
      ∫ z in K, χ z * f z * partialDeriv ψ i z :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
  have he₂ : (∫ z in K, f z * (partialDeriv χ i z * ψ z)) =
      ∫ z in K, partialDeriv χ i z * f z * ψ z :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
  have he₃ : (∫ z in K, g z * (χ z * ψ z)) =
      ∫ z in K, χ z * g z * ψ z :=
    integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
  rw [he₁, he₂, he₃] at hweak
  linarith

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.heatSignedTraceENorm
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Real coordinate L² functions and their weak derivatives embed into
the complex tempered distributions used by the elliptic inverse. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv Manifold ContDiff

noncomputable section


def scalarLocalL2Gradient {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f g : Lp ℝ 2 (volume.restrict K)) (i : Fin 4) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  scalarLocalL2Product hK χ hχ.continuous hc hs g +
    scalarLocalL2PartialProduct hK χ hχ hc hs f i

theorem scalarLocalL2Gradient_pairing {K : Set FourSpace} (hK : MeasurableSet K)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (f g : Lp ℝ 2 (volume.restrict K)) (i : Fin 4)
    (q : 𝓢(FourSpace, ℝ)) :
    (∫ x, scalarLocalL2Gradient hK χ hχ hc hs f g i x * q x) =
      (∫ x, scalarLocalL2Product hK χ hχ.continuous hc hs g x * q x) +
        ∫ x, scalarLocalL2PartialProduct hK χ hχ hc hs f i x * q x := by
  have h₁ := (Lp.memLp (scalarLocalL2Product hK χ hχ.continuous hc hs g)).integrable_mul
    (q.memLp 2 (volume : Measure FourSpace))
  have h₂ := (Lp.memLp (scalarLocalL2PartialProduct hK χ hχ hc hs f i)).integrable_mul
    (q.memLp 2 (volume : Measure FourSpace))
  change Integrable (fun x => scalarLocalL2Product hK χ hχ.continuous hc hs g x * q x) volume at h₁
  change Integrable (fun x => scalarLocalL2PartialProduct hK χ hχ hc hs f i x * q x) volume at h₂
  rw [← integral_add h₁ h₂]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add (scalarLocalL2Product hK χ hχ.continuous hc hs g)
    (scalarLocalL2PartialProduct hK χ hχ hc hs f i)] with x hx
  change (scalarLocalL2Product hK χ hχ.continuous hc hs g +
    scalarLocalL2PartialProduct hK χ hχ hc hs f i) x * q x = _
  rw [hx]
  simp only [Pi.add_apply, add_mul]

theorem scalarLocalL2_complex_derivative {K : Set FourSpace} (hK : MeasurableSet K)
    (f g : Lp ℝ 2 (volume.restrict K)) (i : Fin 4)
    (hw : ∀ (q : FourSpace → ℝ), ContDiff ℝ ∞ q → HasCompactSupport q →
      tsupport q ⊆ K → (∫ z in K, f z * partialDeriv q i z) =
        -(∫ z in K, g z * q z))
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) :
    scalarCoordinateDerivative i
      (scalarComplexL2 (scalarLocalL2Product hK χ hχ.continuous hc hs f) :
        𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 (scalarLocalL2Gradient hK χ hχ hc hs f g i) :
        𝓢'(FourSpace, ℂ)) := by
  apply scalarComplexL2_weak_derivative
  intro q
  rw [scalarLocalL2Gradient_pairing]
  exact scalarLocalL2_weak_product hK f g i hw χ hχ hc hs q (q.smooth ⊤)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Extract a smooth real representative from all local integer Sobolev orders. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff _root_.Topology

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

def halfSmoothCutoff : S :=
  (halfSmoothBump.hasCompactSupport.comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp halfSmoothBump.contDiff)

theorem halfSmoothCutoff_apply (x : V) : halfSmoothCutoff x = (halfSmoothBump x : ℂ) := rfl

theorem halfSmoothCutoff_support :
    tsupport (halfSmoothCutoff : V → ℂ) ⊆ closedBall 0 (1 / 4) := by
  have hs : Function.support (halfSmoothCutoff : V → ℂ) =
      Function.support (halfSmoothBump : V → ℝ) := by
    ext x
    simp only [Function.mem_support, halfSmoothCutoff_apply, ne_eq, Complex.ofReal_eq_zero]
  rw [tsupport, hs]
  change tsupport (halfSmoothBump : V → ℝ) ⊆ _
  rw [halfSmoothBump.tsupport_eq]
  exact Subset.refl _

theorem halfSmoothCutoff_one {x : V} (hx : x ∈ ball 0 (1 / 8)) :
    halfSmoothCutoff x = 1 := by
  change (halfSmoothBump x : ℂ) = 1
  rw [halfSmoothBump.one_of_mem_closedBall (ball_subset_closedBall hx), Complex.ofReal_one]

theorem scalar_half_smooth_real_representative (u : Lp ℝ 2 (volume : Measure V))
    (hreg : ∀ n : ℕ, ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2) →
      MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2 u : T))) :
    ∃ f : V → ℝ, ContDiff ℝ ∞ f ∧
      (u : V → ℝ) =ᵐ[volume.restrict (ball 0 (1 / 8))] f := by
  let φ := halfSmoothCutoff
  have hc : HasCompactSupport (φ : V → ℂ) :=
    (isCompact_closedBall (0 : V) (1 / 4)).of_isClosed_subset (isClosed_tsupport _) halfSmoothCutoff_support
  obtain ⟨f, hf, he⟩ := scalar_L2_cutoff_smooth_on (scalarComplexL2 u) φ
    (ball 0 (1 / 8)) isOpen_ball.measurableSet (fun _ hx => halfSmoothCutoff_one hx)
    (fun n => hreg n φ hc (halfSmoothCutoff_support.trans
      (closedBall_subset_ball (by norm_num))))
  refine ⟨fun x => (f x).re, Complex.reCLM.contDiff.comp hf, ?_⟩
  filter_upwards [he, ae_restrict_of_ae (scalarComplexL2_coe u)] with x hx hu
  have h := congrArg Complex.re hx
  simpa only [hu, Complex.ofReal_re] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Equal local L2 representatives give equal localized distributions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped SchwartzMap

noncomputable section

theorem scalar_localized_distribution_eq (U : Set FourSpace) (hU : MeasurableSet U)
    (u v : Lp ℝ 2 (volume : Measure FourSpace))
    (he : (u : FourSpace → ℝ) =ᵐ[volume.restrict U] v)
    (φ : 𝓢(FourSpace, ℂ)) (hs : tsupport (φ : FourSpace → ℂ) ⊆ U) :
    smulLeftCLM ℂ φ (scalarComplexL2 u : 𝓢'(FourSpace, ℂ)) =
      smulLeftCLM ℂ φ (scalarComplexL2 v : 𝓢'(FourSpace, ℂ)) := by
  ext ψ
  change (scalarComplexL2 u : 𝓢'(FourSpace, ℂ)) (SchwartzMap.smulLeftCLM ℂ φ ψ) =
    (scalarComplexL2 v : 𝓢'(FourSpace, ℂ)) (SchwartzMap.smulLeftCLM ℂ φ ψ)
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hU).mp he, scalarComplexL2_coe u,
    scalarComplexL2_coe v] with x hx hu hv
  rw [SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth, hu, hv]
  by_cases hxU : x ∈ U
  · rw [hx hxU]
  · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hxU (hs ht))
    simp only [hz, zero_smul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The density-weighted unknown in the coordinate Poisson equation has
the same genuine local H¹ regularity as the intrinsic solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set TemperedDistribution
open scoped Manifold ContDiff _root_.Topology SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.weightedCoordinates_frameCompact
omit [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M] in
theorem scalarDensityCutoff_smooth (g : SmoothMetric M) (c : M)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ (chartAt FourSpace c).target) :
    ContDiff ℝ ∞ (fun z => χ z * chartVolumeDensity g c z) :=
  scalarCutoff_contDiff χ (chartVolumeDensity g c) hχ
    (fun z hz => chartVolumeDensity_contDiffAt g c z (hs hz))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Concrete chart and coefficient cutoffs for the local regularity
application. The chart cutoff is one on the whole rescaled unit ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_scalar_chart_cutoff (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c) :
    ∃ χ : FourSpace → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ (chartAt FourSpace c).target ∧
      ∃ η : ℝ, 0 < η ∧ ∀ r : ℝ, |r| < η → ∀ y ∈ closedBall (0 : FourSpace) 1,
        scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target ∧
          χ (scalarRescaledPoint g c z₀ r y) = 1 := by
  obtain ⟨d, hd, hdt⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((chartAt FourSpace c).open_target.mem_nhds z₀.property)
  let χ : ContDiffBump z₀.val :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos hd
      rIn_lt_rOut := half_lt_self hd }
  have hs : tsupport (χ : FourSpace → ℝ) ⊆ (chartAt FourSpace c).target := by
    rw [χ.tsupport_eq]
    exact hdt
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, hs, ?_⟩
  have hone : {z : FourSpace | χ z = 1} ∈ 𝓝 z₀.val := χ.eventuallyEq_one
  have he := scalarRescaledPoint_compact_eventually g c z₀ (isCompact_closedBall 0 1)
    _ hone
  obtain ⟨η, hη, hηs⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨η, hη, ?_⟩
  intro r hr y hy
  have hχ : χ (scalarRescaledPoint g c z₀ r y) = 1 :=
    hηs (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hr) y hy
  refine ⟨hs (subset_tsupport _ ?_), hχ⟩
  exact fun h => zero_ne_one (h.symm.trans hχ)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The rescaled source is the actual smooth scalar and chart density,
with the scale factor dictated by the transformed geometric equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def scalarRescaledSource (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (r : ℝ) (f : SmoothScalar (M := M)) (y : FourSpace) : ℝ :=
  r ^ 2 * chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
    f.val ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))

theorem scalarRescaledPoint_contDiff (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) :
    ContDiff ℝ ∞ (scalarRescaledPoint g c z₀ r) :=
  contDiff_const.add
    (((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ))
      (chartGramMatrix g c 1 z₀)).contDiff.const_smul r)

theorem scalarRescaledSource_contDiffAt (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (f : SmoothScalar (M := M)) (y : FourSpace)
    (hy : scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (scalarRescaledSource g c z₀ r f) y := by
  have hp := (scalarRescaledPoint_contDiff g c z₀ r).contDiffAt (x := y)
  have hf : ContDiffAt ℝ ∞ (fun z => f.val ((chartAt FourSpace c).symm z))
      (scalarRescaledPoint g c z₀ r y) :=
    (f.property.contMDiffAt.comp _
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas c) hy)).contDiffAt
  exact (contDiffAt_const.mul ((chartVolumeDensity_contDiffAt g c _ hy).comp y hp)).mul
    (hf.comp y hp)

theorem scalarRescaledSource_complex_contDiffAt (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (f : SmoothScalar (M := M)) (y : FourSpace)
    (hy : scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (fun x =>
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledSource g c z₀ r f x : ℝ) : ℂ)) y :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp y
    (contDiffAt_const.mul (scalarRescaledSource_contDiffAt g c z₀ r f y hy))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of the actual real rescaled equation with the complex
formal-adjoint equation used by the local regularity theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped Manifold ContDiff SchwartzMap

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_normalized_adjoint_test_equation (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (f : SmoothScalar (M := M))
    (w : Lp ℝ 2 (volume : Measure V)) (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (U : Set V)
    (hU : ∀ x ∈ U, scalarRescaledPoint g c z₀ r x ∈ (chartAt FourSpace c).target)
    (ha : ∀ x ∈ U, ∀ i j, a i j x =
      ((-((2 * Real.pi) ^ 2)⁻¹ *
        (scalarRescaledPrincipal g c z₀ r x i j - (1 : Mat4) i j) : ℝ) : ℂ))
    (hb : ∀ x ∈ U, ∀ i, b i x =
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledDrift g c z₀ r x i : ℝ) : ℂ))
    (hw : ∀ ψ : V → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ x, w x * scalarRescaledOperator g c z₀ r ψ x) =
        ∫ x, scalarRescaledSource g c z₀ r f x * ψ x)
    (φ : S) (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ U) :
    (scalarFormalAdjointOperator a b (scalarComplexL2 w : T) - (scalarComplexL2 w : T)) φ =
      ∫ x, φ x * ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledSource g c z₀ r f x : ℝ) : ℂ) := by
  have hsupport (L : ℂ →L[ℝ] ℝ) : tsupport (L ∘ φ) ⊆ tsupport (φ : V → ℂ) :=
    tsupport_comp_subset L.map_zero φ
  have hcoordinate (L : ℂ →L[ℝ] ℝ) (x : V) :
      L (scalarSchwartzDirectOperator a b φ x - φ x) =
        -((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledOperator g c z₀ r (L ∘ φ) x := by
    by_cases hx : x ∈ tsupport (φ : V → ℂ)
    · exact scalarSchwartzDirectOperator_real_coordinate L
        (scalarRescaledPrincipal g c z₀ r x) (scalarRescaledDrift g c z₀ r x)
        a b φ x (ha x (hs hx)) (hb x (hs hx))
    · rw [scalarSchwartzDirectOperator_zero_off_tsupport a b φ x hx, L.map_zero,
        scalarRescaledOperator_eq_zero_off_tsupport g c z₀ r (L ∘ φ)
          (fun h => hx (hsupport L h)), mul_zero]
  have hcomponent (L : ℂ →L[ℝ] ℝ) :
      L ((scalarFormalAdjointOperator a b (scalarComplexL2 w : T) -
        (scalarComplexL2 w : T)) φ) =
        -((2 * Real.pi) ^ 2)⁻¹ * ∫ x, scalarRescaledSource g c z₀ r f x * L (φ x) := by
    rw [sub_apply, scalarFormalAdjointOperator_pairing, ← map_sub,
      scalarComplexL2_pairing_component]
    change (∫ x, w x * L (scalarSchwartzDirectOperator a b φ x - φ x)) = _
    simp_rw [hcoordinate]
    have hm : (∫ x, w x *
        (-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledOperator g c z₀ r (L ∘ φ) x)) =
        -((2 * Real.pi) ^ 2)⁻¹ *
          ∫ x, w x * scalarRescaledOperator g c z₀ r (L ∘ φ) x := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    rw [hm, hw (L ∘ φ) (L.contDiff.comp (φ.smooth _))
      (hc.comp_left L.map_zero) ((hsupport L).trans hs)]
    rfl
  have hsource (L : ℂ →L[ℝ] ℝ) := scalarComplexSource_pairing_component
    (scalarRescaledSource g c z₀ r f) L φ hc
      (fun x hx => scalarRescaledSource_contDiffAt g c z₀ r f x (hU x (hs hx)))
        (-((2 * Real.pi) ^ 2)⁻¹)
  apply Complex.ext
  · exact (hcomponent Complex.reCLM).trans (hsource Complex.reCLM).symm
  · exact (hcomponent Complex.imCLM).trans (hsource Complex.imCLM).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 forcing term in density-weighted, rescaled coordinates.
Its cutoff is one on the region where the transformed equation is tested. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

def scalarChartSourceL2 (g : SmoothMetric M) (c : M)
    (f : Lp ℝ 2 (normalizedVolume g)) (χ : FourSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (chartAt FourSpace c).target) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarChartL2_cutoff g c f (fun z => χ z * chartVolumeDensity g c z)
    (scalarDensityCutoff_smooth g c χ hχ hs).continuous hc.mul_right
    (tsupport_mul_subset_left.trans hs)).toLp _

theorem scalarChartSourceL2_coe (g : SmoothMetric M) (c : M)
    (f : Lp ℝ 2 (normalizedVolume g)) (χ : FourSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (chartAt FourSpace c).target) :
    scalarChartSourceL2 g c f χ hχ hc hs =ᵐ[volume]
      fun z => χ z * chartVolumeDensity g c z * f ((chartAt FourSpace c).symm z) :=
  MemLp.coeFn_toLp _

def scalarRescaledSourceL2 (g : SmoothMetric M) (c : M)
    (f : Lp ℝ 2 (normalizedVolume g)) (χ : FourSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (chartAt FourSpace c).target)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  r ^ 2 • scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ r hr) z₀
    (scalarChartSourceL2 g c f χ hχ hc hs)

theorem scalarRescaledSourceL2_coe (g : SmoothMetric M) (c : M)
    (f : Lp ℝ 2 (normalizedVolume g)) (χ : FourSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (chartAt FourSpace c).target)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) :
    scalarRescaledSourceL2 g c f χ hχ hc hs z₀ r hr =ᵐ[volume]
      fun y => r ^ 2 * (χ (scalarRescaledPoint g c z₀ r y) *
        chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
        f ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) := by
  let A := scalarRescalingLinearEquiv g c z₀ r hr
  have hq : Measure.QuasiMeasurePreserving (fun y : FourSpace => A y + z₀) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  have hsource := hq.ae_eq_comp (scalarChartSourceL2_coe g c f χ hχ hc hs)
  filter_upwards [Lp.coeFn_smul (r ^ 2)
      (scalarAffinePullbackL2 A z₀ (scalarChartSourceL2 g c f χ hχ hc hs)),
    scalarAffinePullbackL2_coe A z₀ (scalarChartSourceL2 g c f χ hχ hc hs), hsource]
    with y hmul ha hf
  change (r ^ 2 • scalarAffinePullbackL2 A z₀
    (scalarChartSourceL2 g c f χ hχ hc hs)) y = _
  rw [hmul]
  change r ^ 2 * scalarAffinePullbackL2 A z₀ (scalarChartSourceL2 g c f χ hχ hc hs) y = _
  dsimp only [Function.comp_apply] at hf
  rw [ha, hf, scalarRescalingLinearEquiv_apply]

theorem scalarRescaledSourceL2_pairing (g : SmoothMetric M) (c : M)
    (f : Lp ℝ 2 (normalizedVolume g)) (χ : FourSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ (chartAt FourSpace c).target)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) (ψ : FourSpace → ℝ)
    (hone : ∀ y ∈ tsupport ψ, χ (scalarRescaledPoint g c z₀ r y) = 1) :
    (∫ y, scalarRescaledSourceL2 g c f χ hχ hc hs z₀ r hr y * ψ y) =
      ∫ y, r ^ 2 * chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
        f ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y)) * ψ y := by
  apply integral_congr_ae
  filter_upwards [scalarRescaledSourceL2_coe g c f χ hχ hc hs z₀ r hr] with y hy
  rw [hy]
  by_cases hp : y ∈ tsupport ψ
  · rw [hone y hp]
    ring
  · rw [image_eq_zero_of_notMem_tsupport hp]
    ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Density of actual smooth scalar functions in the base L2 space,
needed for the scalar part of the Hodge heat complex. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothScalarContinuous_dense : DenseRange (smoothScalarContinuous (M := M)) := by
  apply Metric.denseRange_iff.mpr
  intro f ε hε
  obtain ⟨a, ha, _⟩ := f.continuous.exists_contMDiff_approx I4 (⊤ : ℕ∞)
    (continuous_const : Continuous (fun _ : M => ε / 2)) (fun _ => half_pos hε)
  refine ⟨⟨a, a.contMDiff⟩, ?_⟩
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (ContinuousMap.dist_le (half_pos hε).le).mpr
  intro x
  change dist (f x) (a x) ≤ ε / 2
  rw [dist_comm]
  exact (ha x).le

variable [SecondCountableTopology M]

theorem smoothScalarBaseL2_dense (g : SmoothMetric M) :
    DenseRange (smoothScalarBaseL2 g) := by
  let := normalizedVolume_isProbability (actual_finitePositiveVolume g)
  have hd := (ContinuousMap.toLp_denseRange ℝ (normalizedVolume g) ℝ (p := 2)
    (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))).comp smoothScalarContinuous_dense
      (ContinuousMap.toLp 2 (normalizedVolume g) ℝ).continuous
  exact hd

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarBaseSmooth_frameCompact
theorem scalarH1BaseValue_dense (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    DenseRange (scalarH1BaseValue g o d) := by
  apply (smoothScalarBaseL2_dense g).mono
  rintro _ ⟨a, rfl⟩
  exact ⟨smoothScalarToH1 d a, scalarH1BaseValue_smooth g o d a⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! Quantitative local elliptic regularity for a real solution in rescaled
chart coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_rescaled_solution_smooth (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (r : ℝ) (f : SmoothScalar (M := M))
    (w : Lp ℝ 2 (volume : Measure V)) (hW : MemSobolev 1 2 (scalarComplexL2 w : T))
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S)
    (htarget : ∀ y ∈ ball (0 : V) 1,
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target)
    (hA : ∀ y ∈ ball (0 : V) 1, ∀ i j, a i j y =
      ((-((2 * Real.pi) ^ 2)⁻¹ *
        (scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j) : ℝ) : ℂ))
    (hB : ∀ y ∈ ball (0 : V) 1, ∀ i, b i y =
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledDrift g c z₀ r y i : ℝ) : ℂ))
    (ha₀ : ∀ i j y, ‖a i j y‖ ≤ scalarEllipticSmallSize)
    (ha₁ : ∀ i j k y, ‖D k (a i j) y‖ ≤ scalarEllipticSmallSize)
    (ha₂ : ∀ i j k l y, ‖D k (D l (a i j)) y‖ ≤ scalarEllipticSmallSize)
    (hb₀ : ∀ j y, ‖scalarAdjointDrift a b j y‖ ≤ scalarEllipticSmallSize)
    (hb₁ : ∀ j k y, ‖D k (scalarAdjointDrift a b j) y‖ ≤ scalarEllipticSmallSize)
    (hreal : ∀ ψ : V → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ ball (0 : V) 1 →
      (∫ y, w y * scalarRescaledOperator g c z₀ r ψ y) =
        ∫ y, scalarRescaledSource g c z₀ r f y * ψ y) :
    ∃ F : V → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      (w : V → ℝ) =ᵐ[volume.restrict (ball (0 : V) (1 / 4))] F := by
  have htests := scalar_normalized_adjoint_test_equation g c z₀ r f w a b
    (ball (0 : V) 1) htarget hA hB hreal
  have hforce (n : ℕ) (ψ : S) (hψc : HasCompactSupport (ψ : V → ℂ))
      (hψs : tsupport (ψ : V → ℂ) ⊆ ball (0 : V) 1) :
      MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ ψ
        (scalarPerturbedOperator a (scalarAdjointDrift a b) (scalarComplexL2 w : T) -
          (scalarComplexL2 w : T) -
            smulLeftCLM ℂ (-scalarAdjointPotential a b : S) (scalarComplexL2 w : T))) := by
    rw [scalarFormalAdjointOperator_remainder]
    exact scalar_localize_smooth_source_memSobolev (ball (0 : V) 1) _ _
      (fun y hy => scalarRescaledSource_complex_contDiffAt g c z₀ r f y (htarget y hy))
      htests ψ hψc hψs n
  have hlocal (ψ : S) (_hc : HasCompactSupport (ψ : V → ℂ))
      (_hs : tsupport (ψ : V → ℂ) ⊆ ball (0 : V) 1) :
      MemSobolev 1 2 (smulLeftCLM ℂ ψ (scalarComplexL2 w : T)) := by
    simpa only [Nat.cast_one] using
      scalar_memSobolev_schwartz_multiplier 1 ψ (scalarComplexL2 w : T)
        (by simpa only [Nat.cast_one] using hW)
  obtain ⟨F, hF, heq⟩ := scalar_small_elliptic_potential_local_real_representative
    a (scalarAdjointDrift a b) scalarEllipticSmallSize scalarEllipticSmallSize_pos.le
    ha₀ ha₁ ha₂ hb₀ hb₁ scalarEllipticSmallSize_small
    (-scalarAdjointPotential a b) (scalarComplexL2 w) hlocal hforce
  refine ⟨F, hF, ?_⟩
  filter_upwards [heq, ae_restrict_of_ae (scalarComplexL2_coe w)] with y hy hw
  rwa [hw, Complex.ofReal_re] at hy

end
end PositiveEinsteinFour.Geometry
end


section

/-! Nondegeneracy and eikonal cancellation on an actual neighborhood of
the origin in the exponential coordinates. No invertibility premise remains
in the neighborhood theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalMetric_pairing (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) (a b : Fin 4 → ℝ) :
    a ⬝ᵥ (heatNormalMetric g o e v *ᵥ b) =
      g.inner (frameExponential g o e v)
        (mfderiv I4 I4 (frameExponential g o e) v (WithLp.toLp 2 a))
        (mfderiv I4 I4 (frameExponential g o e) v (WithLp.toLp 2 b)) := by
  let D : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (frameExponential g o e) v
  let B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ := g.inner (frameExponential g o e v)
  change (∑ i, a i * (heatNormalMetric g o e v *ᵥ b) i) = B (D _) (D _)
  conv_rhs => rw [← sum_coordinateVector a, map_sum, map_sum]
  simp only [map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [heatNormalMetric_row g o e v (WithLp.toLp 2 b) i]
  rfl

theorem heatNormalMetric_posDef (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace)
    (hinj : Function.Injective (mfderiv I4 I4 (frameExponential g o e) v)) :
    (heatNormalMetric g o e v).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact Matrix.isHermitian_iff_isSymm.mpr (heatNormalMetric_symm g o e v)
  · intro a ha
    simp only [star_trivial]
    rw [heatNormalMetric_pairing]
    apply g.pos
    intro hz
    apply ha
    apply WithLp.toLp_injective 2
    apply hinj
    let D : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (frameExponential g o e) v
    change D (WithLp.toLp 2 a) = D 0
    rw [map_zero]
    exact hz

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact positive resolvent of the actual scalar Laplacian on base L2.
It is constructed from the proved H1 inclusion and its Hilbert adjoint. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.baseResolvent_frameCompact
theorem scalarBaseShiftedSolution_weak (f : Lp ℝ 2 (normalizedVolume g)) (v : scalarH1 d) :
    inner ℝ (scalarBaseShiftedSolution g o d f) v = inner ℝ f (scalarH1BaseValue g o d v) :=
  (scalarH1BaseValue g o d).adjoint_inner_left v f

theorem scalarBaseResolvent_symmetric : (scalarBaseResolvent g o d).IsSymmetric := by
  intro f h
  change inner ℝ (scalarH1BaseValue g o d ((scalarH1BaseValue g o d).adjoint f)) h =
    inner ℝ f (scalarH1BaseValue g o d ((scalarH1BaseValue g o d).adjoint h))
  rw [← (scalarH1BaseValue g o d).adjoint_inner_right,
    (scalarH1BaseValue g o d).adjoint_inner_left]

theorem scalarBaseResolvent_energy (f : Lp ℝ 2 (normalizedVolume g)) :
    inner ℝ f (scalarBaseResolvent g o d f) = ‖scalarBaseShiftedSolution g o d f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  exact (scalarBaseShiftedSolution_weak g o d f _).symm

variable [SecondCountableTopology M]

theorem scalarBaseShiftedSolution_injective : Function.Injective (scalarBaseShiftedSolution g o d) := by
  intro f h hfh
  have hp (v : scalarH1 d) : inner ℝ (f - h) (scalarH1BaseValue g o d v) = 0 := by
    rw [← scalarBaseShiftedSolution_weak, map_sub, hfh, sub_self, inner_zero_left]
  have hz : (fun x : Lp ℝ 2 (normalizedVolume g) => inner ℝ (f - h) x) = fun _ => 0 := by
    apply (continuous_const.inner continuous_id).ext_on (scalarH1BaseValue_dense g o d) continuous_const
    rintro _ ⟨v, rfl⟩
    exact hp v
  exact sub_eq_zero.mp (inner_self_eq_zero.mp (congrFun hz (f - h)))

theorem scalarBaseResolvent_pos (f : Lp ℝ 2 (normalizedVolume g)) (hf : f ≠ 0) :
    0 < inner ℝ f (scalarBaseResolvent g o d f) := by
  rw [scalarBaseResolvent_energy, sq_pos_iff, norm_ne_zero_iff]
  intro hz
  exact hf (scalarBaseShiftedSolution_injective g o d (hz.trans (map_zero _).symm))

end
end PositiveEinsteinFour.Geometry
end


section

/-! A linear scalar eigenfunction source remains exactly a multiple of the
weighted chart unknown after localization and affine normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

theorem scalarAffinePullbackL2_smul (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    (κ : ℝ) (w : Lp ℝ 2 (volume : Measure FourSpace)) :
    scalarAffinePullbackL2 A q (κ • w) = κ • scalarAffinePullbackL2 A q w := by
  have hq : Measure.QuasiMeasurePreserving (fun y : FourSpace => A y + q) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  apply Lp.ext
  filter_upwards [scalarAffinePullbackL2_coe A q (κ • w),
    scalarAffinePullbackL2_coe A q w, hq.ae_eq_comp (Lp.coeFn_smul κ w),
    Lp.coeFn_smul κ (scalarAffinePullbackL2 A q w)] with x h₁ h₂ h₃ h₄
  exact h₁.trans (h₃.trans ((congrArg (κ • ·) h₂).symm.trans h₄.symm))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual coefficient operator applied to a C2 family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped ContDiff BigOperators

noncomputable section

theorem fourHeatBundleOperator_joint_continuousAt
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → HeatMat6) (C : FourSpace → HeatMat6)
    (F : ℝ × FourSpace → Fin 6 → ℝ) (z : ℝ × FourSpace)
    (ha : ∀ i j, ContinuousAt (fun x => a x i j) z.2)
    (hb : ∀ i, ContinuousAt (fun x => b x i) z.2)
    (hB : ∀ i k l, ContinuousAt (fun x => B x i k l) z.2)
    (hC : ∀ k l, ContinuousAt (fun x => C x k l) z.2)
    (hF : ∀ k, ContDiffAt ℝ 2 (fun w => F w k) z) (k : Fin 6) :
    ContinuousAt (fun w : ℝ × FourSpace =>
      fourHeatBundleOperator (a w.2) (b w.2) (B w.2) (C w.2)
        (fun x => F (w.1, x)) w.2 k) z := by
  have h1 (i : Fin 4) (l : Fin 6) :=
    (fourHeat_slice_partial_contDiffAt (fun w => F w l) z (hF l) i).continuousAt
  have h2 (i j : Fin 4) (l : Fin 6) :=
    fourHeat_slice_second_continuousAt (fun w => F w l) z (hF l) i j
  have hA (i j : Fin 4) : ContinuousAt (fun w : ℝ × FourSpace => a w.2 i j) z :=
    (ha i j).comp continuousAt_snd
  have hbb (i : Fin 4) : ContinuousAt (fun w : ℝ × FourSpace => b w.2 i) z :=
    (hb i).comp continuousAt_snd
  have hBB (i : Fin 4) (l : Fin 6) :
      ContinuousAt (fun w : ℝ × FourSpace => B w.2 i k l) z :=
    (hB i k l).comp continuousAt_snd
  have hCC (l : Fin 6) : ContinuousAt (fun w : ℝ × FourSpace => C w.2 k l) z :=
    (hC k l).comp continuousAt_snd
  have hS : ContinuousAt (fun w : ℝ × FourSpace => ∑ i : Fin 4, ∑ j : Fin 4,
      a w.2 i j * partialDeriv (partialDeriv (fun x => F (w.1, x) k) i) j w.2) z :=
    tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => (hA i j).mul (h2 i j k)))
  have hT : ContinuousAt (fun w : ℝ × FourSpace => ∑ i : Fin 4,
      b w.2 i * partialDeriv (fun x => F (w.1, x) k) i w.2) z :=
    tendsto_finsetSum _ (fun i _ => (hbb i).mul (h1 i k))
  have hU : ContinuousAt (fun w : ℝ × FourSpace => ∑ i : Fin 4, ∑ l : Fin 6,
      B w.2 i k l * partialDeriv (fun x => F (w.1, x) l) i w.2) z :=
    tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun l _ => (hBB i l).mul (h1 i l)))
  have hV : ContinuousAt (fun w : ℝ × FourSpace => ∑ l : Fin 6,
      C w.2 k l * F w l) z :=
    tendsto_finsetSum _ (fun l _ => (hCC l).mul (hF l).continuousAt)
  exact (((hS.neg.add hT).add (continuousAt_const.mul (hF k).continuousAt)).add hU).add hV

end
end PositiveEinsteinFour.Geometry
end


section

/-! Regularity of the radial transport solver, obtained by differentiating
its actual integral and reconstructing the derivative from four coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped ContDiff BigOperators Interval

noncomputable section

theorem fourHeatRadialAverage_contDiff (n : ℕ) :
    ∀ (m : ℕ) (f : FourSpace → ℝ), ContDiff ℝ (n + 1 : ℕ) f →
      ContDiff ℝ n (fourHeatRadialAverage m f) := by
  induction n with
  | zero =>
    intro m f hf
    apply contDiff_zero.mpr
    have hd : Differentiable ℝ (fourHeatRadialAverage m f) :=
      fun x => (fourHeatRadialAverage_hasFDerivAt m f hf x).differentiableAt
    exact hd.continuous
  | succ n ih =>
    intro m f hf
    have hf1 : ContDiff ℝ 1 f := hf.of_le (by exact_mod_cast Nat.le_add_left 1 (n + 1))
    have hpartial (i : Fin 4) : ContDiff ℝ (n + 1 : ℕ) (partialDeriv f i) :=
      (hf.fderiv_right (m := (n + 1 : ℕ)) (by norm_num [Nat.cast_add, add_assoc])).clm_apply
        (contDiff_const (c := coordinateVector i))
    let D : FourSpace → FourSpace →L[ℝ] ℝ := fun x =>
      ∑ i : Fin 4, fourHeatRadialAverage (m + 1) (partialDeriv f i) x •
        PiLp.proj 2 (fun _ : Fin 4 => ℝ) i
    have hD : ContDiff ℝ n D := by
      apply ContDiff.sum
      intro i _
      exact (ih (m + 1) (partialDeriv f i) (hpartial i)).smul contDiff_const
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨D, hD, ?_⟩
    intro x
    have h := (fourHeatRadialAverage_hasFDerivAt m f hf1 x).differentiableAt.hasFDerivAt
    rwa [fourHeatRadialAverage_fderiv m f hf1 x] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-coordinate density and its leading scalar heat
amplitude. Their normalization is obtained from the differential of the
geometric exponential at zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponentialJacobian_eventually_pos (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) :
    ∀ᶠ v in 𝓝 (0 : FourSpace), 0 < frameExponentialJacobian g o e v := by
  apply (frameExponentialJacobian_continuous g o e).continuousAt.preimage_mem_nhds
  apply isOpen_Ioi.mem_nhds
  rw [mem_Ioi, frameExponentialJacobian_zero]
  norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! Spectral bounds for the actual scalar shifted Laplacian and the
corresponding intrinsic weak eigenvalue equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.baseSpectrum_frameCompact
theorem scalarH1_inner_base (u v : scalarH1 d) :
    inner ℝ u v = inner ℝ (scalarH1BaseValue g o d u) (scalarH1BaseValue g o d v) +
      ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v) := by
  rw [scalarH1_inner]
  have h := (scalarBasePullback g o).inner_map_map (scalarH1BaseValue g o d u)
    (scalarH1BaseValue g o d v)
  rw [scalarH1BaseValue_spec, scalarH1BaseValue_spec] at h
  rw [h]

theorem scalarBaseResolvent_norm_le (f : Lp ℝ 2 (normalizedVolume g)) :
    ‖scalarBaseResolvent g o d f‖ ≤ ‖f‖ := by
  let u := scalarBaseShiftedSolution g o d f
  have he := scalarBaseShiftedSolution_weak g o d f u
  rw [scalarH1_inner_base, real_inner_self_eq_norm_sq] at he
  have hQ : 0 ≤ ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i u) :=
    Finset.sum_nonneg (fun i _ => real_inner_self_nonneg)
  have hC := real_inner_le_norm f (scalarH1BaseValue g o d u)
  change ‖scalarH1BaseValue g o d u‖ ≤ ‖f‖
  nlinarith only [he, hQ, hC, norm_nonneg f, norm_nonneg (scalarH1BaseValue g o d u)]

variable [SecondCountableTopology M]

theorem scalarBaseResolvent_eigenvalue {μ : ℝ}
    (hμ : Module.End.HasEigenvalue (scalarBaseResolvent g o d).toLinearMap μ) :
    0 < μ ∧ μ ≤ 1 := by
  obtain ⟨f, hf⟩ := hμ.exists_hasEigenvector
  have he := Module.End.mem_eigenspace_iff.mp hf.1
  change scalarBaseResolvent g o d f = μ • f at he
  have hp := scalarBaseResolvent_pos g o d f hf.2
  rw [he, real_inner_smul_right] at hp
  have hμpos : 0 < μ := by nlinarith only [hp, real_inner_self_nonneg (x := f)]
  have hn := scalarBaseResolvent_norm_le g o d f
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hμpos] at hn
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf.2
  exact ⟨hμpos, by nlinarith only [hn, hfpos]⟩

theorem scalarBaseResolvent_eigenvector_weak {μ : ℝ} {f : Lp ℝ 2 (normalizedVolume g)}
    (hf : Module.End.HasEigenvector (scalarBaseResolvent g o d).toLinearMap μ f) :
    ∃ u : scalarH1 d, scalarH1BaseValue g o d u = f ∧
      ∀ v : scalarH1 d, (∑ i : Fin 4,
        inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
          (μ⁻¹ - 1) * inner ℝ f (scalarH1BaseValue g o d v) := by
  have hm : μ ≠ 0 := (scalarBaseResolvent_eigenvalue g o d
    (Module.End.hasEigenvalue_of_hasEigenvector hf)).1.ne'
  have he := Module.End.mem_eigenspace_iff.mp hf.1
  change scalarBaseResolvent g o d f = μ • f at he
  let u := μ⁻¹ • scalarBaseShiftedSolution g o d f
  have hu : scalarH1BaseValue g o d u = f := by
    rw [map_smul]
    change μ⁻¹ • scalarBaseResolvent g o d f = f
    rw [he, smul_smul, inv_mul_cancel₀ hm, one_smul]
  refine ⟨u, hu, fun v => ?_⟩
  have hw := scalarBaseShiftedSolution_weak g o d f v
  rw [scalarH1_inner_base] at hw
  change inner ℝ (scalarBaseResolvent g o d f) (scalarH1BaseValue g o d v) + _ = _ at hw
  rw [he, real_inner_smul_left] at hw
  have hscale : (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
      μ⁻¹ * ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i (scalarBaseShiftedSolution g o d f))
        (scalarH1Gradient d i v) := by
    simp only [u, map_smul, real_inner_smul_left, Finset.mul_sum]
  rw [hscale]
  calc
    _ = μ⁻¹ * ((1 - μ) * inner ℝ f (scalarH1BaseValue g o d v)) := by
      congr 1
      linarith only [hw]
    _ = _ := by field_simp [hm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact complex distributional form of the linear rescaled scalar source. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ContDiff

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

theorem scalarComplexL2_scaled_pairing (w : Lp ℝ 2 (volume : Measure V)) (s : ℝ) (φ : S) :
    ∫ y, φ y * ((s * w y : ℝ) : ℂ) = (s : ℂ) * (scalarComplexL2 w : T) φ := by
  rw [Lp.toTemperedDistribution_apply, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [scalarComplexL2_coe w] with y hy
  rw [hy, Complex.ofReal_mul]
  ring

def scalarEigenCutoff (κ : ℝ) : S :=
  scalarCutoffSchwartz scalarCoefficientBump (fun _ => κ)
    scalarCoefficientBump.contDiff scalarCoefficientBump.hasCompactSupport (fun _ _ => contDiffAt_const)

theorem scalarEigenCutoff_on_ball (κ : ℝ) (x : V) (hx : x ∈ ball 0 1) :
    scalarEigenCutoff κ x = (κ : ℂ) := by
  change ((scalarCoefficientBump x * κ : ℝ) : ℂ) = _
  rw [scalarCoefficientBump_one (ball_subset_closedBall hx), one_mul]

theorem scalar_eigen_source_pairing (w F : Lp ℝ 2 (volume : Measure V)) (s k : ℝ)
    (hF : F = k • w) (φ : S) :
    ∫ y, φ y * ((s * F y : ℝ) : ℂ) = ((s * k : ℝ) : ℂ) * (scalarComplexL2 w : T) φ := by
  rw [scalarComplexL2_scaled_pairing, hF]
  have he := scalarComplexL2_real_smul_distribution k w
  rw [he]
  simp only [smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Solving the inhomogeneous radial transport equation by the actual
integral with a nonvanishing leading amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff

noncomputable section

theorem fourHeatWeightedRadialAverage_contDiff (n m : ℕ) (U F : FourSpace → ℝ)
    (hU : ContDiff ℝ (n + 1 : ℕ) U) (hF : ContDiff ℝ (n + 1 : ℕ) F)
    (hU0 : ∀ y, U y ≠ 0) : ContDiff ℝ n (fourHeatWeightedRadialAverage m U F) := by
  exact (hU.of_le (by exact_mod_cast Nat.le_succ n)).mul
    (fourHeatRadialAverage_contDiff n m _ (hF.div hU hU0))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact subtraction identities for localized sources in the scalar
resolvent chain. Density weighting and affine pullback preserve the equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set TemperedDistribution
open scoped Manifold ContDiff SchwartzMap

noncomputable section

theorem scalarAffinePullbackL2_sub (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    (u v : Lp ℝ 2 (volume : Measure FourSpace)) :
    scalarAffinePullbackL2 A q (u - v) =
      scalarAffinePullbackL2 A q u - scalarAffinePullbackL2 A q v := by
  have hq : Measure.QuasiMeasurePreserving (fun y : FourSpace => A y + q) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  apply Lp.ext
  filter_upwards [scalarAffinePullbackL2_coe A q (u - v),
    scalarAffinePullbackL2_coe A q u, scalarAffinePullbackL2_coe A q v,
    hq.ae_eq_comp (Lp.coeFn_sub u v),
    Lp.coeFn_sub (scalarAffinePullbackL2 A q u) (scalarAffinePullbackL2 A q v)]
    with x hsub hu hv he hp
  exact hsub.trans (he.trans ((congrArg₂ (· - ·) hu hv).symm.trans hp.symm))

theorem scalarComplexL2_sub_distribution (u v : Lp ℝ 2 (volume : Measure FourSpace)) :
    (scalarComplexL2 (u - v) : 𝓢'(FourSpace, ℂ)) =
      (scalarComplexL2 u : 𝓢'(FourSpace, ℂ)) - (scalarComplexL2 v : 𝓢'(FourSpace, ℂ)) := by
  have he : scalarComplexL2 (u - v) = scalarComplexL2 u - scalarComplexL2 v :=
    (Complex.ofRealCLM.compLpₗ (p := 2) (μ := volume)).map_sub u v
  rw [he]
  exact (Lp.toTemperedDistributionCLM ℂ volume 2).map_sub _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseHeatRate_nonneg
    (μ : ScalarBaseEigenIndex g o d) : 0 ≤ scalarBaseHeatRate g o d μ :=
  sub_nonneg.mpr ((one_le_inv₀ (scalarBaseResolvent_eigenvalue g o d μ.1.property).1).mpr
    (scalarBaseResolvent_eigenvalue g o d μ.1.property).2)

def scalarBaseHeatWeight (t : ℝ≥0)
    (μ : ScalarBaseEigenIndex g o d) : ℝ :=
  Real.exp (-(t : ℝ) * scalarBaseHeatRate g o d μ)

theorem scalarBaseHeatWeight_bound (t : ℝ≥0)
    (μ : ScalarBaseEigenIndex g o d) : |scalarBaseHeatWeight g o d t μ| ≤ 1 := by
  rw [scalarBaseHeatWeight, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg)
    (scalarBaseHeatRate_nonneg g o d μ)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar drift coefficients vary jointly in the actual normal
family; their slice is the geometric density drift. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyDrift (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (j : Fin 4) : ℝ :=
  -((∑ i : Fin 4, heatFamilyScalarPartial (fun y => (heatFamilyMetric g c P y)⁻¹ i j) i z) +
    (heatFamilyDensity g c P z)⁻¹ * ∑ i : Fin 4,
      (heatFamilyMetric g c P z)⁻¹ i j * heatFamilyScalarPartial (heatFamilyDensity g c P) i z)

theorem heatFamilyDrift_slice (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ 2 P z) (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hdet : 0 < (heatFamilyMetric g c P z).det) (j : Fin 4) :
    heatFamilyDrift g c P z j =
      fourHeatDensityDrift (fun x => (heatFamilyMetric g c P (x, z.2))⁻¹)
        (fun x => heatFamilyDensity g c P (x, z.2)) z.1 j := by
  have hA (i : Fin 4) : DifferentiableAt ℝ
      (fun y => (heatFamilyMetric g c P y)⁻¹ i j) z :=
    (heatFamilyInverse_contDiffAt 1 g c P z hP hz hdet.ne' i j).differentiableAt one_ne_zero
  have hJ : DifferentiableAt ℝ (heatFamilyDensity g c P) z :=
    (heatFamilyDensity_contDiffAt 1 g c P z hP hz hdet.ne').differentiableAt one_ne_zero
  simp only [heatFamilyDrift, fourHeatDensityDrift,
    heatFamilyScalarPartial_slice _ z hJ,
    heatFamilyScalarPartial_slice _ z (hA _)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

omit [SecondCountableTopology M] in
theorem scalarBaseHeatWeight_continuous
    (μ : ScalarBaseEigenIndex g o d) :
    Continuous (fun t : ℝ≥0 => scalarBaseHeatWeight g o d t μ) := by
  change Continuous (fun t : ℝ≥0 => Real.exp (-(t : ℝ) * scalarBaseHeatRate g o d μ))
  exact Real.continuous_exp.comp (continuous_subtype_val.neg.mul_const _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar spectral multipliers and heat evolution for the actual metric. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

theorem scalarBaseHeatPowerWeight_bound (t : ℝ≥0) (ht : 0 < t)
    (n : ℕ) (μ : ScalarBaseEigenIndex g o d) :
    |μ.1.val⁻¹ ^ n * scalarBaseHeatWeight g o d t μ| ≤
      Real.exp t * (n.factorial : ℝ) / (t : ℝ) ^ n := by
  have htR : 0 < (t : ℝ) := ht
  have hm := (scalarBaseResolvent_eigenvalue g o d μ.1.property).1
  change 0 < μ.1.val at hm
  have hy : 0 ≤ (t : ℝ) * μ.1.val⁻¹ := mul_nonneg htR.le (inv_pos.mpr hm).le
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have he := (div_le_iff₀ hn).mp
    (Real.pow_div_factorial_le_exp ((t : ℝ) * μ.1.val⁻¹) hy n)
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-((t : ℝ) * μ.1.val⁻¹))).le
  have heq : (Real.exp ((t : ℝ) * μ.1.val⁻¹) * (n.factorial : ℝ)) *
      Real.exp (-((t : ℝ) * μ.1.val⁻¹)) = (n.factorial : ℝ) := by
    rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [heq] at he'
  have hw : scalarBaseHeatWeight g o d t μ =
      Real.exp t * Real.exp (-((t : ℝ) * μ.1.val⁻¹)) := by
    rw [scalarBaseHeatWeight, scalarBaseHeatRate, ← Real.exp_add]
    congr 1
    ring
  rw [hw, abs_of_pos (mul_pos (pow_pos (inv_pos.mpr hm) n)
    (mul_pos (Real.exp_pos _) (Real.exp_pos _)))]
  calc
    _ = (Real.exp t / (t : ℝ) ^ n) *
        (((t : ℝ) * μ.1.val⁻¹) ^ n * Real.exp (-((t : ℝ) * μ.1.val⁻¹))) := by
      rw [mul_pow]
      field_simp [ne_of_gt htR]
    _ ≤ (Real.exp t / (t : ℝ) ^ n) * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left he' (by positivity)
    _ = _ := by ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar and matrix coefficients of the two-form heat
operator form one finite-regularity family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyZero (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace) : HeatMat6 :=
  heatFamilyPotential g c P z +
    (∑ i : Fin 4, heatFamilyDrift g c P z i • heatFamilyTwoFormConnection g c P i z) -
    ∑ i : Fin 4, ∑ j : Fin 4, (heatFamilyMetric g c P z)⁻¹ i j •
      ((Matrix.of fun k l => heatFamilyScalarPartial
        (fun y => heatFamilyTwoFormConnection g c P i y k l) j z) +
        heatFamilyTwoFormConnection g c P j z * heatFamilyTwoFormConnection g c P i z)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar and matrix coefficients of the one-form heat
operator form one finite-regularity family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def heatFamilyOneZero (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace) : Mat4 :=
  ((3 : ℝ) • (1 : Mat4)) +
    (∑ i : Fin 4, heatFamilyDrift g c P z i • heatFamilyConnection g c P i z) -
    ∑ i : Fin 4, ∑ j : Fin 4, (heatFamilyMetric g c P z)⁻¹ i j •
      ((Matrix.of fun k l => heatFamilyScalarPartial
        (fun y => heatFamilyConnection g c P i y k l) j z) +
        heatFamilyConnection g c P j z * heatFamilyConnection g c P i z)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The concrete shifted scalar resolvent supplies the local elliptic chain.
No regularity of its L2 input is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.resolventChain_frameCompact
def scalarBaseResolventJet (n : ℕ) (f : Lp ℝ 2 (normalizedVolume g)) : scalarH1 d :=
  scalarBaseShiftedSolution g o d ((scalarBaseResolvent g o d ^ n) f)

theorem scalarBaseResolventJet_value (n : ℕ) (f : Lp ℝ 2 (normalizedVolume g)) :
    scalarH1BaseValue g o d (scalarBaseResolventJet g o d n f) =
      (scalarBaseResolvent g o d ^ (n + 1)) f := by
  rw [pow_succ']
  rfl

theorem scalarBaseResolventJet_weak (k : ℕ) (f : Lp ℝ 2 (normalizedVolume g)) (v : scalarH1 d) :
    (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i (scalarBaseResolventJet g o d (k + 1) f))
      (scalarH1Gradient d i v)) =
      inner ℝ (scalarH1BaseValue g o d (scalarBaseResolventJet g o d k f) -
        scalarH1BaseValue g o d (scalarBaseResolventJet g o d (k + 1) f))
          (scalarH1BaseValue g o d v) := by
  have he := scalarBaseShiftedSolution_weak g o d ((scalarBaseResolvent g o d ^ (k + 1)) f) v
  change inner ℝ (scalarBaseResolventJet g o d (k + 1) f) v = _ at he
  rw [scalarH1_inner_base, ← scalarBaseResolventJet_value] at he
  rw [inner_sub_left]
  linarith only [he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar heat coefficients are actual integrals. Their finite
regularity and transport equations follow from the radial integral solver. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeatCoefficient_contDiff (m : ℕ) : ∀ (n : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ) (c U : FourSpace → ℝ),
    (∀ i j, ContDiff ℝ (n + 3 * m : ℕ) (fun x => a x i j)) →
    (∀ i, ContDiff ℝ (n + 3 * m : ℕ) (fun x => b x i)) →
    ContDiff ℝ (n + 3 * m : ℕ) c → ContDiff ℝ (n + 3 * m : ℕ) U →
    (∀ x, U x ≠ 0) → ContDiff ℝ n (fourHeatCoefficient a b c U m) := by
  induction m with
  | zero =>
    intro n a b c U ha hb hc hU hU0
    simpa only [fourHeatCoefficient, mul_zero, add_zero] using hU
  | succ m ih =>
    intro n a b c U ha hb hc hU hU0
    have he : n + 3 * (m + 1) = (n + 3) + 3 * m := by omega
    have hreg : ContDiff ℝ (n + 3 : ℕ) (fourHeatCoefficient a b c U m) :=
      ih (n + 3) a b c U (fun i j => he ▸ ha i j) (fun i => he ▸ hb i)
        (he ▸ hc) (he ▸ hU) hU0
    have hle : ((n + 1 : ℕ) : ℕ∞ω) ≤ (n + 3 * (m + 1) : ℕ) := by
      exact_mod_cast (show n + 1 ≤ n + 3 * (m + 1) by omega)
    apply fourHeatWeightedRadialAverage_contDiff n m U _ (hU.of_le hle) _ hU0
    apply ContDiff.neg
    apply fourHeatLocalOperator_contDiff (n + 1) a b c _
      (fun i j => (ha i j).of_le hle) (fun i => (hb i).of_le hle) (hc.of_le hle)
    simpa only [Nat.add_assoc] using hreg

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite scalar chain rules and the actual change of normal-coordinate
Laplacian. The Jacobian derivative cancels the density drift exactly. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scalar_finite_chart_laplacian (g : SmoothMetric M) {f : M → ℝ}
    (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (c : M) (z : ChartTarget c) :
    scalarLaplacianBase g f ((chartAt FourSpace c).symm z) =
      scalarChartOperator g c (fun y => f ((chartAt FourSpace c).symm y)) z := by
  have hc := scalar_finite_derivative_transition g hf c ((chartAt FourSpace c).symm z)
    2 (by omega) z z.property (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rw [chartTransitionMatrix_to_center c z z.property] at hc
  have he : chartScalarLaplacian g f c z =
      scalarLaplacianBase g f ((chartAt FourSpace c).symm z) := by
    rw [chartScalarLaplacian, hc]
    simp_rw [← frameTensor_mul]
    exact scalarLaplacian_eq_base g f (chartGramSection g c 1 (by simp) z)
  rw [← he, chartScalarLaplacian_coefficients g f c z z.property]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual L2 values and Laplacians of C4 cutoffs. Their spectral pairing
is obtained from the finite-regularity geometric Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarFinite_probability
def scalarFiniteLaplacianL2 (f : M → ℝ) (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) :
    Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ
    ⟨scalarLaplacianBase g f, scalar_finite_laplacian_continuous hf⟩

omit [SecondCountableTopology M] in
theorem scalarFiniteLaplacianL2_coe (f : M → ℝ) (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) :
    scalarFiniteLaplacianL2 g f hf =ᵐ[normalizedVolume g] scalarLaplacianBase g f :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g) _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth scalar eigenfunctions are total in H1, not merely L2. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_8
omit [SecondCountableTopology M] in
theorem scalarH1BaseValue_injective : Function.Injective (scalarH1BaseValue g o d) := by
  intro u v h
  apply scalarH1Value_injective d
  exact (scalarH1BaseValue_spec g o d u).symm.trans
    ((congrArg (scalarBasePullback g o) h).trans (scalarH1BaseValue_spec g o d v))

omit [SecondCountableTopology M] in
theorem scalarBaseShiftedSolution_dense : DenseRange (scalarBaseShiftedSolution g o d) :=
  adjoint_denseRange_of_injective _ (scalarH1BaseValue_injective g o d)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact spatial slices of the lower order family coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatConnectionZero_germ (a : Mat4) (b : Fin 4 → ℝ)
    {A A' : Fin 4 → FourSpace → HeatMat6} (V : HeatMat6) {x : FourSpace}
    (hA : ∀ i, A i =ᶠ[𝓝 x] A' i) :
    fourHeatConnectionZero a b A V x = fourHeatConnectionZero a b A' V x := by
  have hv (i : Fin 4) : A i x = A' i x := (hA i).self_of_nhds
  have hd (i j : Fin 4) (k l : Fin 6) :
      partialDeriv (fun y => A i y k l) j x = partialDeriv (fun y => A' i y k l) j x :=
    fourHeat_partial_germ ((hA i).mono fun y hy => congrArg (fun B : HeatMat6 => B k l) hy) j
  simp only [fourHeatConnectionZero, hv, hd]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar local heat operator is the negative geometric Laplacian
in the actual normal chart. Both its inverse metric and drift are derived. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.scalar_operator_pullback (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det) (u : FourSpace → ℝ)
    (hu : ContDiffAt ℝ 2 u (D.point x).1) :
    fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
      (fun y => u (D.point y).1) x = -scalarChartOperator g c u (D.point x).1 := by
  let F := fun y => (D.point y).1
  let J := jacobianMatrix F x
  let A := (heatNormalMetric g o e x)⁻¹
  let H := (metricInChart g c (D.point x).1)⁻¹
  let Q : Mat4 := fun r s => partialDeriv (partialDeriv u r) s (F x)
  let S := fun r => partialDeriv u r (F x)
  have hA : J * A * Jᵀ = H := D.inverseMetric_transport x hx hs hd.ne'
  have hb := D.drift_transport_at x hx hP hs hd
  have h := heat_rough_trace_algebra J A H Q
    (fun i => matrixPartial (jacobianMatrix F) i x) (heatNormalDrift g o e x) S
    (fun r => ∑ p, ∑ q, H p q * christoffel g c (F x) r p q) hA
    (fun i j r => heatJacobian_partials_commute hP.fst r j i) hb
  have hf (i : Fin 4) : partialDeriv (fun y => u (D.point y).1) i x =
      ∑ r, J r i * S r :=
    partialDeriv_comp (hP.fst.differentiableAt (by norm_num))
      (hu.differentiableAt (by norm_num)) i
  have hsecond (i j : Fin 4) :
      partialDeriv (partialDeriv (fun y => u (D.point y).1) i) j x =
        (∑ r, matrixPartial (jacobianMatrix F) j x r i * S r) +
          ∑ r, ∑ s, J r i * J s j * Q r s :=
    heat_scalar_second_comp F u x hP.fst hu i j
  change -(∑ i, ∑ j, A i j *
    partialDeriv (partialDeriv (fun y => u (D.point y).1) i) j x) +
      (∑ i, heatNormalDrift g o e x i * partialDeriv (fun y => u (D.point y).1) i x) +
        0 * u (D.point x).1 = _
  simp only [zero_mul, add_zero, hf, hsecond]
  rw [h, heat_connection_trace_expand]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  have hH : H s r = H r s := by
    exact congrArg (fun B : Mat4 => B r s)
      (show Hᵀ = H by
        dsimp only [H]
        rw [Matrix.transpose_nonsing_inv]
        congr 1
        ext a b
        exact metricInChart_comm g c (D.point x).1 b a)
  rw [hH]
  change H r s * (partialDeriv (partialDeriv u s) r (F x) -
    ∑ k, christoffel g c (F x) k s r * partialDeriv u k (F x)) = _
  simp only [christoffel_comm g c (F x) _ s r]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first two jets of the actual radial integral at its center.
These are the local derivatives used in the second heat coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeatRadialAverage_partial_zero (m : ℕ) (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 1 f) (i : Fin 4) :
    partialDeriv (fourHeatRadialAverage m f) i 0 = partialDeriv f i 0 / (m + 2 : ℝ) := by
  rw [fourHeatRadialAverage_partial m f hf, fourHeatRadialAverage_zero]
  push_cast
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity and finite time polynomials for the actual six-component
differential expression. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatBundleOperator_const_mul (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (r : ℝ)
    (u : FourSpace → Fin 6 → ℝ) (x : FourSpace) (k : Fin 6) :
    fourHeatBundleOperator a b B C (fun y l => r * u y l) x k =
      r * fourHeatBundleOperator a b B C u x k := by
  unfold fourHeatBundleOperator fourHeatBundleFirst fourHeatBundleZero
  simp only [fourHeatLocalOperator_const_mul, fourHeat_partial_const_mul]
  have hB : (∑ i : Fin 4, ∑ l : Fin 6,
      B i k l * (r * partialDeriv (fun y => u y l) i x)) =
      r * (∑ i : Fin 4, ∑ l : Fin 6, B i k l * partialDeriv (fun y => u y l) i x) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hC : (∑ l : Fin 6, C k l * (r * u x l)) =
      r * (∑ l : Fin 6, C k l * u x l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hB, hC]
  ring

theorem fourHeatBundlePolynomial_operator (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6)
    (u : Fin 4 → FourSpace → Fin 6 → ℝ)
    (hu : ∀ m k, ContDiff ℝ 2 (fun x => u m x k)) (t : ℝ) (x : FourSpace) (k : Fin 6) :
    fourHeatBundleOperator a b B C (fourHeatBundlePolynomial u t) x k =
      fourHeatBundleOperator a b B C (u 0) x k +
        t * fourHeatBundleOperator a b B C (u 1) x k +
        t ^ 2 * fourHeatBundleOperator a b B C (u 2) x k +
        t ^ 3 * fourHeatBundleOperator a b B C (u 3) x k := by
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  have h3 := hu 3
  unfold fourHeatBundlePolynomial fourHeatPolynomial
  rw [fourHeatBundleOperator_add a b B C _ _
      (fun l => ((h0 l).add (contDiff_const.mul (h1 l))).add (contDiff_const.mul (h2 l)))
      (fun l => contDiff_const.mul (h3 l)),
    fourHeatBundleOperator_add a b B C _ _
      (fun l => (h0 l).add (contDiff_const.mul (h1 l)))
      (fun l => contDiff_const.mul (h2 l)),
    fourHeatBundleOperator_add a b B C _ _ h0 (fun l => contDiff_const.mul (h1 l))]
  simp only [fourHeatBundleOperator_const_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Successive matrix heat amplitudes are actual radial integrals of the
preceding amplitude under the four-component differential operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatOneCoefficient_center (m : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → Mat4) (C : FourSpace → Mat4) (U : FourSpace → ℝ)
    (hU0 : U 0 ≠ 0) (k l : Fin 4) :
    (m + 1 : ℝ) * fourHeatOneCoefficient a b B C U (m + 1) 0 k l =
      -fourHeatOneOperator (a 0) (b 0) (B 0) (C 0)
        (fun y q => fourHeatOneCoefficient a b B C U m y q l) 0 k := by
  simp only [fourHeatOneCoefficient, fourHeatWeightedRadialAverage, fourHeatRadialAverage_zero]
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual time derivative of a Gaussian polynomial can be passed
through every continuous compactly supported scalar pairing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped _root_.Topology

noncomputable section

theorem fourHeatGaussianPolynomialTime_continuousOn (u : Fin 4 → FourSpace → ℝ)
    (hu : ∀ m, Continuous (u m)) :
    ContinuousOn (fun z : ℝ × FourSpace => fourHeatGaussianPolynomialTime u z.1 z.2)
      (Ioi 0 ×ˢ univ) := by
  have hQ : Continuous (fun z : ℝ × FourSpace => fourHeatPolynomialTime u z.1 z.2) := by
    exact (((hu 1).comp continuous_snd).add
      ((continuous_const.mul continuous_fst).mul ((hu 2).comp continuous_snd))).add
      ((continuous_const.mul (continuous_fst.pow 2)).mul ((hu 3).comp continuous_snd))
  exact ((fourHeatGaussianTimeFactor_joint_continuousOn.mul fourHeatGaussian_joint_continuousOn).mul
    (fourHeatPolynomial_joint_continuous u hu).continuousOn).add
    (fourHeatGaussian_joint_continuousOn.mul hQ.continuousOn)

theorem fourHeat_compact_polynomial_pairing_deriv
    (ψ : FourSpace → ℝ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (u : Fin 4 → FourSpace → ℝ) (hu : ∀ m, Continuous (u m))
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, ψ x * (fourHeatGaussian s x * fourHeatPolynomial u s x))
      (∫ x, ψ x * fourHeatGaussianPolynomialTime u t x) t := by
  apply fourHeat_compact_time_integral
    (fun s x => ψ x * (fourHeatGaussian s x * fourHeatPolynomial u s x))
    (fun s x => ψ x * fourHeatGaussianPolynomialTime u s x) (tsupport ψ) hc
  · intro s _hs
    exact hψ.mul ((fourHeatGaussian_continuous s).mul
      ((fourHeatPolynomial_joint_continuous u hu).comp (continuous_const.prodMk continuous_id)))
  · exact (hψ.comp continuous_snd).continuousOn.mul (fourHeatGaussianPolynomialTime_continuousOn u hu)
  · intro s _hs x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · intro s _hs x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · intro s hs x
    exact (fourHeatGaussianPolynomial_hasDerivAt u s hs x).const_mul (ψ x)
  · exact ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two center derivatives of the actual weighted radial solver.
These finite jets determine the second heat coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeatWeightedRadialAverage_partial_zero (m : ℕ) (U F : FourSpace → ℝ)
    (hU : ContDiff ℝ 2 U) (hF : ContDiff ℝ 2 F) (hU0 : ∀ x, U x ≠ 0) (i : Fin 4) :
    partialDeriv (fourHeatWeightedRadialAverage m U F) i 0 =
      partialDeriv U i 0 * ((F 0 / U 0) / (m + 1 : ℝ)) +
      U 0 * (partialDeriv (fun x => F x / U x) i 0 / (m + 2 : ℝ)) := by
  have hQ : ContDiff ℝ 2 (fun y => F y / U y) := hF.div hU hU0
  have hR := fourHeatRadialAverage_preserves_contDiff 2 m _ hQ
  change partialDeriv (fun x => U x * fourHeatRadialAverage m (fun y => F y / U y) x) i 0 = _
  rw [scalar_partial_product U (fourHeatRadialAverage m (fun y => F y / U y)) 0 (hU.differentiable (by norm_num)).differentiableAt
    (hR.differentiable (by norm_num)).differentiableAt i,
    fourHeatRadialAverage_zero,
    fourHeatRadialAverage_partial_zero m _ (hQ.of_le (by norm_num))]

end
end PositiveEinsteinFour.Geometry
end


section

/-! At the center of the normal frame, the zeroth-order bundle coefficient
is precisely the intrinsic Weitzenböck potential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.curvature_center {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    heatNormalFrameCurvature g c D.point 0 = twoFormMetricCurvatureTensor g e := by
  rw [D.curvature_as_actual 0 (mem_ball_self D.radius_pos), D.frame_zero he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first connection jet in radial gauge is alternating in the
radial and derivative indices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_partial_second_sum_four (F : Fin 4 → FourSpace → ℝ) (x : FourSpace)
    (hF : ∀ k, ContDiffAt ℝ 2 (F k) x) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun y => ∑ k, F k y) i) j x =
      ∑ k, partialDeriv (partialDeriv (F k) i) j x := by
  have hn : ∀ᶠ y in 𝓝 x, ∀ k, DifferentiableAt ℝ (F k) y := by
    apply eventually_all.mpr
    intro k
    filter_upwards [(hF k).eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have he : partialDeriv (fun y => ∑ k, F k y) i =ᶠ[𝓝 x]
      (fun y => ∑ k, partialDeriv (F k) i y) := by
    filter_upwards [hn] with y hy
    exact heat_partial_sum_four F y hy i
  rw [fourHeat_partial_germ he j]
  apply heat_partial_sum_four
  intro k
  exact (((hF k).fderiv_right (m := 1) (by norm_num)).clm_apply
    (contDiffAt_const (c := coordinateVector i))).differentiableAt one_ne_zero

theorem heat_radial_first_jet_alternating (A : Fin 4 → FourSpace → ℝ)
    (hA : ∀ k, ContDiffAt ℝ 2 (A k) 0)
    (hR : (fun x : FourSpace => ∑ k, x k * A k x) =ᶠ[𝓝 0] fun _ => 0)
    (i j : Fin 4) :
    partialDeriv (A i) j 0 + partialDeriv (A j) i 0 = 0 := by
  let R := fun x : FourSpace => ∑ k, x k * A k x
  have he : partialDeriv R i =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hR.eventuallyEq_nhds] with x hx
    rw [fourHeat_partial_germ hx i]
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  have hzero : partialDeriv (partialDeriv R i) j 0 = 0 := by
    rw [fourHeat_partial_germ he j]
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  have hf (k : Fin 4) : ContDiffAt ℝ 2 (fun y : FourSpace => y k * A k y) 0 :=
    (EuclideanSpace.proj k).contDiff.contDiffAt.mul (hA k)
  rw [heat_partial_second_sum_four _ 0 hf i j] at hzero
  have hprod (k : Fin 4) :
      partialDeriv (partialDeriv (fun y : FourSpace => y k * A k y) i) j 0 =
        (if i = k then 1 else 0) * partialDeriv (A k) j 0 +
        (if j = k then 1 else 0) * partialDeriv (A k) i 0 := by
    have hc : ContDiffAt ℝ 2 (fun y : FourSpace => y k) 0 :=
      (EuclideanSpace.proj k : FourSpace →L[ℝ] ℝ).contDiff.contDiffAt
    rw [scalar_partial_second_product_at (fun y : FourSpace => y k) (A k) 0
      hc (hA k) i j,
      heat_partial_coordinate, heat_partial_coordinate, heat_partial_second_coordinate]
    simp
  simp_rw [hprod] at hzero
  simpa only [Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, if_true] using hzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! Four C4 scalar transport amplitudes. Ten derivatives of the
extended normal coefficients give four derivatives of each amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {e : FrameBundle g}

theorem HeatNormalExtension.scalarAmplitude_zero (E : HeatNormalExtension 10 g o e) :
    E.scalarAmplitude 0 0 = 1 :=
  E.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! At the center the first radial connection jet is one half of the
actual curvature endomorphism, with the derivative order explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.frame_connection_first_jet
    (D : HeatNormalFrameData g o c e) (i j k l : Fin 4) :
    partialDeriv (fun x => heatNormalFrameConnection g c D.point i x k l) j 0 +
      partialDeriv (fun x => heatNormalFrameConnection g c D.point j x k l) i 0 = 0 := by
  apply heat_radial_first_jet_alternating
    (fun a x => heatNormalFrameConnection g c D.point a x k l) _ _ i j
  · intro a
    exact (D.connection_regular a k l).of_le (by norm_num)
  · filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    have h := congrArg (fun B : Mat4 => B k l) (D.radial_connection x hx)
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second order remainder needed for the signed Gaussian coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Asymptotics Set
open scoped _root_.Topology

noncomputable section


theorem fourHeat_second_order_remainder_at (f : FourSpace → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) :
    (fun x => f x - f 0 - fderiv ℝ f 0 x -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 x x)
      =o[𝓝 0] (fun x : FourSpace => ‖x‖ ^ 2) := by
  obtain ⟨F, hF, _, he⟩ := heatScalar_extension 2 f hf
  have hd : fderiv ℝ F =ᶠ[𝓝 0] fderiv ℝ f :=
    he.eventuallyEq_nhds.mono (fun _ h => h.fderiv_eq)
  apply (fourHeat_second_order_remainder F hF).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [he] with x hx
  rw [hx, he.self_of_nhds, he.fderiv_eq, hd.fderiv_eq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first diagonal bundle amplitude is its scalar contribution minus
the actual Weitzenböck potential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatBundleOperator_initial (a : Mat4) (b : Fin 4 → ℝ)
    (C : HeatMat6) (U : FourSpace → ℝ) (x : FourSpace) (k l : Fin 6) :
    fourHeatBundleOperator a b (fun _ => 0) C
      (fun y q => U y * (if q = l then 1 else 0)) x k =
    (if k = l then 1 else 0) * fourHeatLocalOperator a b 0 U x + U x * C k l := by
  have hf : (fun y => U y * (if k = l then 1 else 0)) =
      (fun y => (if k = l then 1 else 0) * U y) := by funext y; ring
  unfold fourHeatBundleOperator fourHeatBundleFirst fourHeatBundleZero
  rw [hf, fourHeatLocalOperator_const_mul]
  simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first actual one-form amplitude contains the Ricci potential 3 Id. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOneOperator_initial (a : Mat4) (b : Fin 4 → ℝ)
    (C : Mat4) (U : FourSpace → ℝ) (x : FourSpace) (k l : Fin 4) :
    fourHeatOneOperator a b (fun _ => 0) C
      (fun y q => U y * (if q = l then 1 else 0)) x k =
    (if k = l then 1 else 0) * fourHeatLocalOperator a b 0 U x + U x * C k l := by
  have hf : (fun y => U y * (if k = l then 1 else 0)) =
      (fun y => (if k = l then 1 else 0) * U y) := by funext y; ring
  unfold fourHeatOneOperator fourHeatOneFirst fourHeatOneZero
  rw [hf, fourHeatLocalOperator_const_mul]
  simp only [Matrix.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true]
  ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.oneConnection_diagonal_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (i k l : Fin 4) :
    partialDeriv (fun x => heatNormalFrameConnection g c D.point i x k l) i 0 = 0 := by
  have h := D.frame_connection_first_jet i i k l
  linarith only [h]

theorem HeatNormalFrameData.oneZero_center {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e) :
    heatNormalOneZero D 0 = (3 : ℝ) • (1 : Mat4) := by
  ext k l
  simp [heatNormalOneZero, fourHeatOneConnectionZero, heatNormalMetric_zero,
    D.frame_connection_zero, D.oneConnection_diagonal_zero, Matrix.one_apply]

theorem HeatNormalOneExtension.first_amplitude_center {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) :
    E.amplitude 1 0 =
      (-fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 E.base.U 0) • (1 : Mat4) -
        ((3 : ℝ) • (1 : Mat4)) := by
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hB : E.B 0 = fun _ => 0 := by
    funext i
    exact congrFun E.B_near.self_of_nhds i |>.trans (D.oneFirst_zero i)
  have hC : E.C 0 = ((3 : ℝ) • (1 : Mat4)) :=
    E.C_near.self_of_nhds.trans D.oneZero_center
  ext k l
  have hrec := fourHeatOneCoefficient_center 0 E.base.a E.base.b E.B E.C E.base.U
    (by rw [hU]; exact one_ne_zero) k l
  have hrec' : E.amplitude 1 0 k l =
    -fourHeatOneOperator (E.base.a 0) (E.base.b 0) (E.B 0) (E.C 0)
      (fun y q => E.base.U y * (if q = l then 1 else 0)) 0 k := by
    simpa only [Nat.cast_zero, zero_add, one_mul] using! hrec
  rw [hB, hC, fourHeatOneOperator_initial, hU] at hrec'
  change E.amplitude 1 0 k l =
    -fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 E.base.U 0 *
      (if k = l then 1 else 0) - ((3 : ℝ) • (1 : Mat4)) k l
  linarith only [hrec']

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates07
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual smooth closed and coclosed two-forms. Their inclusion in the
finite weak Hodge kernel proves finite-dimensionality without an index input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem smoothHarmonicTwoForm_energy_zero (u : smoothTwoForms o)
    (hu : u ∈ smoothHarmonicTwoForms) : smoothTwoFormDeRhamEnergy u = 0 := by
  obtain ⟨hd, hc⟩ := (mem_smoothHarmonicTwoForms u).mp hu
  have he (e : FrameBundle g) : twoFormDeRhamQuadratic (fun i j k =>
      twoFormFramedCovariantDerivative o u.val e ![i,j,k]) = 0 := by
    change (1 / 6 : ℝ) * (∑ i, ∑ j, ∑ k, smoothTwoFormExterior u e i j k ^ 2) +
      (∑ k, smoothTwoFormCodifferential u e k ^ 2) = 0
    simp only [hd, hc, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero,
      mul_zero, add_zero]
  unfold smoothTwoFormDeRhamEnergy
  simp only [he, integral_zero]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Dilation and domination of a bounded amplitude with vanishing first jet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Asymptotics Set
open scoped _root_.Topology

noncomputable section

theorem fourHeat_vanishing_scaled_limit (f : FourSpace → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0)
    (z : FourSpace) :
    Tendsto (fun t : ℝ => f (Real.sqrt t • z) / t) (𝓝[>] 0)
      (𝓝 ((1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 z z)) := by
  let B := fderiv ℝ (fderiv ℝ f) 0
  have hr : (fun x => f x - (1 / 2 : ℝ) * B x x)
      =o[𝓝 0] (fun x : FourSpace => ‖x‖ ^ 2) := by
    simpa [hf0, hD0, B] using fourHeat_second_order_remainder_at f hf
  have hs : Tendsto (fun t : ℝ => Real.sqrt t • z) (𝓝[>] 0)
      (𝓝 (0 : FourSpace)) := by
    simpa using ((Real.continuous_sqrt.tendsto 0).smul
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => z) (𝓝 (0 : ℝ)) (𝓝 z))).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  by_cases hz : z = 0
  · subst z
    simp [hf0]
  have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hh := ((hr.comp_tendsto hs).tendsto_div_nhds_zero).mul_const (‖z‖ ^ 2)
  simp only [zero_mul] at hh
  have hh' : Tendsto (fun t : ℝ => f (Real.sqrt t • z) / t - (1 / 2 : ℝ) * B z z)
      (𝓝[>] 0) (𝓝 0) := by
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    dsimp only [Function.comp_apply]
    rw [fourHeat_norm_sqrt_smul_sq t ht.le]
    simp only [map_smul, _root_.smul_apply, smul_eq_mul]
    have hsq := Real.sq_sqrt ht.le
    field_simp [ht.ne', hnz]
    rw [hsq]
    ring
  have h := hh'.add_const ((1 / 2 : ℝ) * B z z)
  simpa only [sub_add_cancel, zero_add] using h

theorem fourHeat_vanishing_quadratic_bound (f : FourSpace → ℝ)
    (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖f x‖ ≤ K * ‖x‖ ^ 2 := by
  let B := fderiv ℝ (fderiv ℝ f) 0
  have hr : (fun x => f x - (1 / 2 : ℝ) * B x x)
      =o[𝓝 0] (fun x : FourSpace => ‖x‖ ^ 2) := by
    simpa [hf0, hD0, B] using fourHeat_second_order_remainder_at f hf
  obtain ⟨δ, hδ, he⟩ := Metric.eventually_nhds_iff.mp (hr.bound zero_lt_one)
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  refine ⟨1 + ‖B‖ + C / δ ^ 2, by positivity, fun x => ?_⟩
  by_cases hx : ‖x‖ < δ
  · have he' := he (by simpa [dist_zero_right] using hx)
    simp only [one_mul, norm_pow, norm_norm] at he'
    have hb := B.le_opNorm₂ x x
    have hhalf : ‖(1 / 2 : ℝ) * B x x‖ ≤ ‖B‖ * ‖x‖ ^ 2 := by
      rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc
        (1 / 2 : ℝ) * ‖B x x‖ ≤ ‖B x x‖ := by nlinarith [norm_nonneg (B x x)]
        _ ≤ ‖B‖ * ‖x‖ ^ 2 := by nlinarith [hb]
    calc
      ‖f x‖ ≤ ‖f x - (1 / 2 : ℝ) * B x x‖ + ‖(1 / 2 : ℝ) * B x x‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ ‖x‖ ^ 2 + ‖B‖ * ‖x‖ ^ 2 := add_le_add he' hhalf
      _ ≤ (1 + ‖B‖ + C / δ ^ 2) * ‖x‖ ^ 2 := by
        have hdiv : 0 ≤ C / δ ^ 2 := by positivity
        nlinarith [mul_nonneg hdiv (sq_nonneg ‖x‖)]
  · have hxδ : δ ≤ ‖x‖ := le_of_not_gt hx
    have hratio : C ≤ (C / δ ^ 2) * ‖x‖ ^ 2 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
      exact mul_le_mul_of_nonneg_left (show δ ^ 2 ≤ ‖x‖ ^ 2 by nlinarith) hC0
    calc
      ‖f x‖ ≤ C := hC x
      _ ≤ (C / δ ^ 2) * ‖x‖ ^ 2 := hratio
      _ ≤ (1 + ‖B‖ + C / δ ^ 2) * ‖x‖ ^ 2 := by
        nlinarith [mul_nonneg (norm_nonneg B) (sq_nonneg ‖x‖)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform compact bounds for the actual transport family and the
coefficient left by the third transport equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

def HeatFamilySmoothCoefficients.lastCoefficient (E : HeatFamilySmoothCoefficients)
    (z : HeatRadialFrameSpace) (k l : Fin 6) : ℝ :=
  heatFamilyBundleOperator E.a E.b E.B E.C (fun y q => E.amplitude 3 y q l) z k

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exterior derivative of an actual smooth one-form is closed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneFormExterior_closed (hRic : RicciThree g) (u : smoothCovariantFields M 1) :
    smoothTwoFormExterior (smoothOneFormExterior (o := o) u) = 0 := by
  funext e i j k
  change twoFormExteriorComponent (fun p q r =>
    twoFormFramedCovariantDerivative o (smoothOneFormExterior (o := o) u).val e ![p,q,r]) i j k = 0
  unfold twoFormExteriorComponent
  have hD (p q r : Fin 4) := smoothOneFormExterior_covariant (o := o) hRic u e p q r
  simp only [hD]
  let X := covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val)) e
  let A := covariantFieldFramed g u.val e
  let R := frameCurvature g e.base e.frame
  apply exterior_second_zero X A R ?_ (frame_algebraic_firstBianchi e.frame)
  intro p q r
  have h := u.property.framed_commutator (g := g) e p q ![r]
  change X ![p,q,r] - X ![q,p,r] = -tensorSlotAction (curvatureEndomorphism R p q) A ![r] at h
  rw [tensorSlotAction_one] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exterior/codifferential energy is a continuous nonnegative scalar
on the base. Its vanishing detects actual smooth harmonic forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.continuous_framedDeRhamDensity {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) : Continuous (fun e : FrameBundle g =>
      twoFormDeRhamQuadratic (fun i j k => twoFormFramedCovariantDerivative o u e ![i,j,k])) := by
  have hD (i j k : Fin 4) : Continuous (fun e => twoFormFramedCovariantDerivative o u e ![i,j,k]) :=
    (continuous_apply _).comp hu.continuous_framedCovariantDerivative
  apply Continuous.add
  · apply continuous_const.mul
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro k _
    exact (((hD i j k).sub (hD j i k)).add (hD k i j)).pow 2
  · apply continuous_finsetSum
    intro k _
    exact ((continuous_finsetSum _ (fun i _ => hD i i k)).neg).pow 2

theorem TwoFormSmooth.continuous_deRhamDensity {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) : Continuous (twoFormDeRhamDensity o u) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  apply (hu.continuous_framedDeRhamDensity.continuousAt.comp
    (continuousAt_localGramSection g c 1 (by simp))).congr_of_eventuallyEq
  filter_upwards [] with x
  have he := twoFormDeRhamDensity_eq_frame (o := o) u (localGramSection g c 1 (by simp) x)
  rw [localGramSection_base] at he
  exact he

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureNormalizedVolume
theorem smoothTwoFormDeRhamEnergy_eq_base (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy u = ∫ x, twoFormDeRhamDensity o u.val x ∂normalizedVolume g := by
  have hi := u.property.continuous_deRhamDensity.integrable_of_hasCompactSupport
    (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
  rw [← canonicalFrameMeasure_integral_base g o _ hi]
  apply integral_congr_ae
  filter_upwards [] with e
  exact (twoFormDeRhamDensity_eq_frame u.val e).symm

theorem smoothTwoFormDeRhamEnergy_eq_zero_iff (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy u = 0 ↔ u ∈ smoothHarmonicTwoForms := by
  constructor
  · intro h
    let _ := normalizedVolume_isOpenPosMeasure g
    have hn (x : M) : 0 ≤ twoFormDeRhamDensity o u.val x := twoFormDeRhamQuadratic_nonneg _
    have hc := u.property.continuous_deRhamDensity
    have hi := hc.integrable_of_hasCompactSupport
      (μ := normalizedVolume g) (HasCompactSupport.of_compactSpace _)
    rw [smoothTwoFormDeRhamEnergy_eq_base] at h
    have ha := (integral_eq_zero_iff_of_nonneg hn hi).mp h
    have hz : twoFormDeRhamDensity o u.val = 0 := Measure.eq_of_ae_eq ha hc continuous_const
    apply (mem_smoothHarmonicTwoForms u).mpr
    have hf (e : FrameBundle g) := congrFun hz e.base
    simp only [twoFormDeRhamDensity_eq_frame, Pi.zero_apply] at hf
    constructor
    · intro e i j k
      exact ((twoFormDeRhamQuadratic_eq_zero _).mp (hf e)).1 i j k
    · intro e k
      exact ((twoFormDeRhamQuadratic_eq_zero _).mp (hf e)).2 k
  · exact smoothHarmonicTwoForm_energy_zero u

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second-order Gaussian limit, with the actual Euclidean normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology BigOperators

noncomputable section

theorem fourHeatGaussian_second_order_limit (f : FourSpace → ℝ)
    (hc : Continuous f) (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun t : ℝ => (∫ x : FourSpace, fourHeatGaussian t x * f x) / t)
      (𝓝[>] 0) (𝓝 (∑ i, fderiv ℝ (fderiv ℝ f) 0 (coordinateVector i) (coordinateVector i))) := by
  obtain ⟨K, _, hK⟩ := fourHeat_vanishing_quadratic_bound f hf hf0 hD0 C hC
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ z : FourSpace,
      ‖fourHeatGaussian 1 z * (f (Real.sqrt t • z) / t)‖ ≤
        K * (‖z‖ ^ 2 * fourHeatGaussian 1 z) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Eventually.of_forall fun z => by
      rw [norm_mul, norm_div, Real.norm_of_nonneg (fourHeatGaussian_pos 1 zero_lt_one z).le,
        Real.norm_of_nonneg ht.le]
      have hscale : ‖f (Real.sqrt t • z)‖ / t ≤ K * ‖z‖ ^ 2 := by
        apply (div_le_iff₀ ht).mpr
        calc
          ‖f (Real.sqrt t • z)‖ ≤ K * ‖Real.sqrt t • z‖ ^ 2 := hK _
          _ = K * ‖z‖ ^ 2 * t := by rw [fourHeat_norm_sqrt_smul_sq t ht.le]; ring
      calc
        _ ≤ fourHeatGaussian 1 z * (K * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hscale (fourHeatGaussian_pos 1 zero_lt_one z).le
        _ = _ := by ring
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun z : FourSpace => fourHeatGaussian 1 z * (f (Real.sqrt t • z) / t)) volume := by
    apply Continuous.aestronglyMeasurable
    exact (fourHeatGaussian_continuous 1).mul
      ((hc.comp
        ((continuous_const : Continuous (fun _ : FourSpace => Real.sqrt t)).smul continuous_id)).div_const t)
  have hpoint (z : FourSpace) :=
    (fourHeat_vanishing_scaled_limit f hf hf0 hD0 z).const_mul (fourHeatGaussian 1 z)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure FourSpace)) (l := 𝓝[>] (0 : ℝ))
    (F := fun t z => fourHeatGaussian 1 z * (f (Real.sqrt t • z) / t))
    (f := fun z => fourHeatGaussian 1 z * ((1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 z z))
    (fun z => K * (‖z‖ ^ 2 * fourHeatGaussian 1 z)) (Eventually.of_forall hmeas) hbound
    ((fourHeatGaussian_moment_integrable 1 1 zero_lt_one).const_mul K)
    (Eventually.of_forall hpoint)
  rw [fourHeatGaussian_bilinear_integral] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hd := fourHeatGaussian_integral_dilate t ht (fun x => f (-x) / t) 0
  simp only [zero_sub, neg_neg] at hd
  simpa only [← mul_div_assoc, integral_div] using hd.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual adjoint relation between d on one-forms and δ on two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_10
theorem smoothOneFormExterior_adjoint (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothOneFormExterior (o := o) u) v =
      ∫ e, ∑ j, covariantFieldFramed g u.val e ![j] *
        smoothTwoFormCodifferential v e j ∂canonicalFrameMeasure g o := by
  let μ := canonicalFrameMeasure g o
  let A := fun i j e => covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j] *
    twoFormFramedValue o v.val e ![i,j]
  let B := fun i j e => covariantFieldFramed g u.val e ![j] *
    twoFormFramedCovariantDerivative o v.val e ![i,i,j]
  have hA (i j : Fin 4) : Integrable (A i j) μ :=
    (((continuous_apply _).comp u.property.derivative.continuous_framed).mul
      ((continuous_apply _).comp v.property.continuous_framedValue)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hB (i j : Fin 4) : Integrable (B i j) μ :=
    (((continuous_apply _).comp u.property.continuous_framed).mul
      ((continuous_apply _).comp v.property.continuous_framedCovariantDerivative)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have ha : (∫ e, ∑ i, ∑ j, A i j e ∂μ) = -(∫ e, ∑ j, ∑ i, B i j e ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hA i j)),
      integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun i _ => hB i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hA _ j),
      integral_finsetSum _ (fun i _ => hB i _)]
    have hg (i j : Fin 4) : (∫ e, A i j e ∂μ) = -(∫ e, B i j e ∂μ) :=
      smoothOneForm_direction_green hRic u v i j
    simp_rw [hg, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  have he : smoothTwoFormL2Inner (smoothOneFormExterior (o := o) u) v =
      ∫ e, ∑ i, ∑ j, A i j e ∂μ := by
    rw [smoothTwoFormL2Inner_eq_frame]
    apply integral_congr_ae
    filter_upwards [] with e
    exact smoothOneFormExterior_frame_pairing u v e
  rw [he, ha, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with e
  change -(∑ j, ∑ i, B i j e) = ∑ j, covariantFieldFramed g u.val e ![j] *
    -(∑ i, twoFormFramedCovariantDerivative o v.val e ![i,i,j])
  simp only [B, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]

theorem smoothHarmonic_orthogonal_exact (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (v : smoothTwoForms o)
    (hv : v ∈ smoothHarmonicTwoForms) :
    smoothTwoFormL2Inner (smoothOneFormExterior (o := o) u) v = 0 := by
  have hc := ((mem_smoothHarmonicTwoForms v).mp hv).2
  rw [smoothOneFormExterior_adjoint hRic]
  simp only [hc, mul_zero, Finset.sum_const_zero, integral_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts for the first covariant derivatives of actual
smooth one-forms, and their Ricci commutator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.oneFormGreenCompactFrames
theorem oneForm_derivative_green (hRic : RicciThree g)
    (u v : smoothCovariantFields M 1) (i j k l : Fin 4) :
    (∫ e, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j] *
      covariantFieldFramed g (covariantFieldDerivative g v.val) e ![k,l]
        ∂canonicalFrameMeasure g o) =
      -(∫ e, covariantFieldFramed g u.val e ![j] *
        covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g v.val))
          e ![i,k,l] ∂canonicalFrameMeasure g o) := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => covariantFieldFramed g u.val e ![j],
    (continuous_apply _).comp u.property.continuous_framed⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,j],
    (continuous_apply _).comp u.property.derivative.continuous_framed⟩
  let H : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g v.val) e ![k,l],
    (continuous_apply _).comp v.property.derivative.continuous_framed⟩
  let DH : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g v.val))
      e ![i,k,l],
    (continuous_apply _).comp v.property.derivative.derivative.continuous_framed⟩
  apply scalar_flow_green (d := d.toMetricGreenData) i F DF H DH
  · intro t e
    exact u.property.parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![j]
  · intro t e
    exact v.property.derivative.parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![k,l]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic codifferential density and the four-dimensional Hodge
splitting of the actual de Rham energy density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormDeRhamDensity_hodge (u : smoothTwoForms o) (x : M) :
    twoFormDeRhamDensity o u.val x =
      twoFormCodiffDensity u x + twoFormCodiffDensity (smoothTwoFormHodge o u) x := by
  obtain ⟨S, hS, U, hU, hxU, hUt, hp⟩ := twoForm_positive_chart o x
  let z := chartAt FourSpace x x
  let e := chartGramSection g x S hS ⟨z, hUt hxU⟩
  have hb : e.base = x := (chartAt FourSpace x).left_inv (mem_chart_source FourSpace x)
  rw [← hb, twoFormDeRhamDensity_eq_frame, twoFormCodiffDensity_eq_frame u e,
    twoFormCodiffDensity_eq_frame (smoothTwoFormHodge o u) e]
  have hplain := u.property.gramCovariantDerivative x S hS U hU hUt hp z hxU
  have hstar := (smoothTwoFormHodge o u).property.gramCovariantDerivative
    x S hS U hU hUt hp z hxU
  rw [hplain, hstar]
  have hr : twoFormLocalNablaRows (g := g) x S
      (twoFormChartValue o (smoothTwoFormHodge o u).val x S hS) z =
      fun i => twoFormHodge (twoFormLocalNablaRows (g := g) x S
        (twoFormChartValue o u.val x S hS) z i) := by
    funext i
    exact u.property.localNablaRows_hodge x S hS U hU hUt hp z hxU i
  rw [hr, twoFormCodiffTensor_squareNorm, twoFormCodiffTensor_squareNorm]
  exact twoForm_rows_deRham_hodge _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differentiated codifferential and the actual exact dδ term. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormDDelta_closed (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormExterior (smoothTwoFormDDelta u) = 0 :=
  smoothOneFormExterior_closed hRic (smoothTwoFormCodifferentialField u)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two surviving orders of the signed squared-Gaussian integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology BigOperators

noncomputable section

theorem fourHeatGaussian_square_first_order_limit (f : FourSpace → ℝ)
    (hc : Continuous f) (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun t : ℝ => t * ∫ x : FourSpace, fourHeatGaussian t x ^ 2 * f x)
      (𝓝[>] 0) (𝓝 ((1 / (128 * Real.pi ^ 2)) *
        ∑ i, fderiv ℝ (fderiv ℝ f) 0 (coordinateVector i) (coordinateVector i))) := by
  have h := ((fourHeatGaussian_second_order_limit f hc hf hf0 hD0 C hC).comp
    fourHeatGaussian_half_tendsto).const_mul (1 / (128 * Real.pi ^ 2))
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have he := fourHeatGaussian_square_weighted f t ht
  dsimp only [Function.comp_apply]
  field_simp [ht.ne'] at he ⊢
  nlinarith [he]

theorem fourHeat_signed_gaussian_limit (f : FourSpace → ℝ)
    (hc : Continuous f) (hf : ContDiffAt ℝ 2 f 0) (hf0 : f 0 = 0) (hD0 : fderiv ℝ f 0 = 0)
    (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (F : ℝ → FourSpace → ℝ)
    (hF : Continuous (fun z : ℝ × FourSpace => F z.1 z.2))
    (B T : ℝ) (hT : 0 < T) (hB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖F t x‖ ≤ B) :
    Tendsto (fun t : ℝ => ∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
      (2 * t * f x + t ^ 2 * F t x)) (𝓝[>] 0)
      (𝓝 ((1 / (64 * Real.pi ^ 2)) *
        ((∑ i, fderiv ℝ (fderiv ℝ f) 0 (coordinateVector i) (coordinateVector i)) + F 0 0))) := by
  have h := ((fourHeatGaussian_square_first_order_limit f hc hf hf0 hD0 C hC).const_mul 2).add
    (fourHeatGaussian_square_family_limit F hF B T hT hB)
  have hval : 2 * ((1 / (128 * Real.pi ^ 2)) *
      ∑ i, fderiv ℝ (fderiv ℝ f) 0 (coordinateVector i) (coordinateVector i)) +
      (1 / (64 * Real.pi ^ 2)) * F 0 0 =
      (1 / (64 * Real.pi ^ 2)) *
        ((∑ i, fderiv ℝ (fderiv ℝ f) 0 (coordinateVector i) (coordinateVector i)) + F 0 0) := by
    ring
  rw [hval] at h
  apply h.congr'
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioc (0 : ℝ) T := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t ht hlt
    exact ⟨ht, hlt.le⟩
  filter_upwards [hsmall] with t ht
  have hi := fourHeatGaussian_square_amplitude_integrable f hc C hC t ht.1
  have hFi := fourHeatGaussian_square_amplitude_integrable (F t)
    (hF.comp (continuous_const.prodMk continuous_id)) B (hB t ⟨ht.1.le, ht.2⟩) t ht.1
  have he : (fun x : FourSpace => fourHeatGaussian t x ^ 2 * (2 * t * f x + t ^ 2 * F t x)) =
      fun x => (2 * t) * (fourHeatGaussian t x ^ 2 * f x) +
        t ^ 2 * (fourHeatGaussian t x ^ 2 * F t x) := by funext x; ring
  rw [he, integral_add (hi.const_mul _) (hFi.const_mul _), integral_const_mul, integral_const_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The rough equation for an actual closed and coclosed smooth one-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem oneForm_closed_second_symmetric (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (hu : smoothOneFormExterior (o := o) u = 0)
    (e : FrameBundle g) (i j k : Fin 4) :
    covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![i,j,k] =
      covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        e ![i,k,j] := by
  have h := smoothOneFormExterior_covariant (o := o) hRic u e i j k
  rw [hu] at h
  have hz : twoFormFramedCovariantDerivative o (0 : M → TwoFormFour) e = 0 := by
    simpa only [zero_smul] using
      twoFormFramedCovariantDerivative_smul (o := o) (0 : ℝ) (0 : M → TwoFormFour) e
  change twoFormFramedCovariantDerivative o (0 : M → TwoFormFour) e ![i,j,k] = _ at h
  rw [hz, Pi.zero_apply] at h
  exact sub_eq_zero.mp h.symm

include o in
theorem oneForm_trace_second_zero (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (hu : ∀ e, (∑ i, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i]) = 0)
    (e : FrameBundle g) (j : Fin 4) :
    (∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
      e ![j,i,i]) = 0 := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow j).map t e
  have hzero : γ 0 = e := actualParallelMetricData_zero g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic j e
  have hDu : CovariantFieldSmooth (covariantFieldDerivative g u.val) := u.property.derivative
  have hidx (i : Fin 4) : Fin.cons j ![i,i] = ![j,i,i] := by
    ext k
    fin_cases k <;> rfl
  have hd : HasDerivAt
      (fun t => ∑ i, covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![i,i])
      (∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
        (γ 0) ![j,i,i]) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    simpa only [hidx] using hDu.parallel_derivative (g := g) γ 0 j
      (d.curve_continuous j e).continuousAt (d.parallelCurve j 0 e) ![i,i]
  have he : (fun t => ∑ i, covariantFieldFramed g (covariantFieldDerivative g u.val) (γ t) ![i,i]) =
      fun _ => (0 : ℝ) := funext (fun t => hu (γ t))
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  simpa only [hzero] using hz

theorem oneForm_harmonic_rough (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (hclosed : smoothOneFormExterior (o := o) u = 0)
    (hcoclosed : ∀ e, (∑ i, covariantFieldFramed g
      (covariantFieldDerivative g u.val) e ![i,i]) = 0)
    (e : FrameBundle g) (j : Fin 4) :
    (∑ i, covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
      e ![i,i,j]) = 3 * covariantFieldFramed g u.val e ![j] := by
  have hc := oneForm_ricci_commutator hRic u e j
  rw [Finset.sum_sub_distrib, oneForm_trace_second_zero (o := o) hRic u hcoclosed e j,
    sub_zero] at hc
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i _
  exact oneForm_closed_second_symmetric hRic u hclosed e i i j

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth one-form divergence has mean zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.oneFormDivergenceCompactFrames
theorem oneForm_derivative_integral_zero (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (i : Fin 4) :
    (∫ e, covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i]
      ∂canonicalFrameMeasure g o) = 0 := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => covariantFieldFramed g u.val e ![i],
    (continuous_apply _).comp u.property.continuous_framed⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i],
    (continuous_apply _).comp u.property.derivative.continuous_framed⟩
  apply Averages.integral_flow_derivative_zero (canonicalFrameMeasure g o)
    (d.flow i).map (d.flow i).continuous (d.flow i).preserves F DF
  intro t e
  exact u.property.parallel_derivative (fun s => (d.flow i).map s e) t i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![i]

theorem oneFormDivergence_mean_zero (hRic : RicciThree g) (u : smoothCovariantFields M 1) :
    (∫ e, oneFormDivergence g u e.base ∂canonicalFrameMeasure g o) = 0 := by
  have hi (i : Fin 4) : Integrable (fun e =>
      covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i])
      (canonicalFrameMeasure g o) := by
    have hDu : CovariantFieldSmooth (covariantFieldDerivative g u.val) := u.property.derivative
    have hc : Continuous (fun e =>
        covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i]) :=
      (continuous_apply _).comp (hDu.continuous_framed (g := g))
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [oneFormDivergence_eq_frame]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [oneForm_derivative_integral_zero hRic u, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The codifferential bilinear form and the global Hodge energy splitting. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_12
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureNormalizedVolume_1
theorem smoothTwoFormDeRhamEnergy_codiff (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy u = twoFormCodiffPairing u u +
      twoFormCodiffPairing (smoothTwoFormHodge o u) (smoothTwoFormHodge o u) := by
  rw [smoothTwoFormDeRhamEnergy_eq_base]
  simp_rw [twoFormDeRhamDensity_hodge]
  rw [integral_add
    ((twoFormCodiffDensity_continuous u).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((twoFormCodiffDensity_continuous (smoothTwoFormHodge o u)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)), ← twoFormCodiffPairing_self, ← twoFormCodiffPairing_self]

theorem smoothTwoFormDDelta_pairing (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothTwoFormDDelta u) v = twoFormCodiffPairing u v := by
  apply Eq.trans (smoothOneFormExterior_adjoint hRic (smoothTwoFormCodifferentialField u) v)
  apply integral_congr_ae
  filter_upwards [] with e
  apply Finset.sum_congr rfl
  intro k _
  rw [smoothTwoFormCodifferentialField_component]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive Ricci curvature kills the actual closed and coclosed
smooth one-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.oneFormBochnerCompactFrames
theorem oneForm_harmonic_component_integral (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (hclosed : smoothOneFormExterior (o := o) u = 0)
    (hcoclosed : ∀ e, (∑ i, covariantFieldFramed g
      (covariantFieldDerivative g u.val) e ![i,i]) = 0) (j : Fin 4) :
    (∫ e, covariantFieldFramed g u.val e ![j] ^ 2 ∂canonicalFrameMeasure g o) = 0 := by
  have he : (∑ i, ∫ e, covariantFieldFramed g (covariantFieldDerivative g u.val)
      e ![i,j] ^ 2 ∂canonicalFrameMeasure g o) =
      -3 * ∫ e, covariantFieldFramed g u.val e ![j] ^ 2 ∂canonicalFrameMeasure g o := by
    calc
      _ = ∑ i, -(∫ e, covariantFieldFramed g u.val e ![j] *
          covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
            e ![i,i,j] ∂canonicalFrameMeasure g o) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [pow_two] using oneForm_derivative_green (o := o) hRic u u i j i j
      _ = -(∫ e, ∑ i, covariantFieldFramed g u.val e ![j] *
          covariantFieldFramed g (covariantFieldDerivative g (covariantFieldDerivative g u.val))
            e ![i,i,j] ∂canonicalFrameMeasure g o) := by
        rw [integral_finsetSum _ (fun i _ => oneForm_secondPair_integrable (o := o) u i j)]
        rw [Finset.sum_neg_distrib]
      _ = -(∫ e, 3 * covariantFieldFramed g u.val e ![j] ^ 2 ∂canonicalFrameMeasure g o) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with e
        rw [← Finset.mul_sum, oneForm_harmonic_rough hRic u hclosed hcoclosed e j]
        ring
      _ = _ := by rw [integral_const_mul]; ring
  have hgrad : 0 ≤ ∑ i, ∫ e, covariantFieldFramed g (covariantFieldDerivative g u.val)
      e ![i,j] ^ 2 ∂canonicalFrameMeasure g o :=
    Finset.sum_nonneg (fun i _ => integral_nonneg (fun e => sq_nonneg _))
  have hv : 0 ≤ ∫ e, covariantFieldFramed g u.val e ![j] ^ 2 ∂canonicalFrameMeasure g o :=
    integral_nonneg (fun e => sq_nonneg _)
  linarith only [he, hgrad, hv]

theorem oneForm_harmonic_eq_zero (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (hclosed : smoothOneFormExterior (o := o) u = 0)
    (hcoclosed : ∀ e, (∑ i, covariantFieldFramed g
      (covariantFieldDerivative g u.val) e ![i,i]) = 0) : u = 0 := by
  apply oneForm_eq_zero_of_norm_integral
  rw [oneForm_norm_integral (o := o) u,
    integral_finsetSum _ (fun j _ => oneForm_valueSquare_integrable (o := o) u j)]
  simp only [oneForm_harmonic_component_integral hRic u hclosed hcoclosed,
    Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar differential and minus divergence are adjoint. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarOneFormCompactFrames
theorem scalar_oneForm_direction_green (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) (u : smoothCovariantFields M 1) (i : Fin 4) :
    (∫ e, scalarGradient g f.val e i * covariantFieldFramed g u.val e ![i]
      ∂canonicalFrameMeasure g o) =
    -(∫ e, f.val e.base *
      covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i]
        ∂canonicalFrameMeasure g o) := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => f.val e.base,
    f.property.continuous.comp (continuous_frameBase g)⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e => scalarGradient g f.val e i,
    actual_scalarGradient_continuous g f.property i⟩
  let H : C(FrameBundle g, ℝ) := ⟨fun e => covariantFieldFramed g u.val e ![i],
    (continuous_apply _).comp u.property.continuous_framed⟩
  let DH : C(FrameBundle g, ℝ) := ⟨fun e =>
    covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i],
    (continuous_apply _).comp u.property.derivative.continuous_framed⟩
  apply scalar_flow_green (d := d.toMetricGreenData) i F DF H DH
  · intro t e
    exact actual_scalarValue_parallel_derivative g f.property _ t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e)
  · intro t e
    exact u.property.parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) ![i]

theorem scalar_oneForm_adjoint (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) (u : smoothCovariantFields M 1) :
    (∫ e, ∑ i, scalarGradient g f.val e i * covariantFieldFramed g u.val e ![i]
      ∂canonicalFrameMeasure g o) =
    -(∫ e, f.val e.base * oneFormDivergence g u e.base ∂canonicalFrameMeasure g o) := by
  have hL (i : Fin 4) : Integrable (fun e =>
      scalarGradient g f.val e i * covariantFieldFramed g u.val e ![i])
      (canonicalFrameMeasure g o) :=
    ((actual_scalarGradient_continuous g f.property i).mul
      ((continuous_apply _).comp u.property.continuous_framed)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hR (i : Fin 4) : Integrable (fun e => f.val e.base *
      covariantFieldFramed g (covariantFieldDerivative g u.val) e ![i,i])
      (canonicalFrameMeasure g o) :=
    ((f.property.continuous.comp (continuous_frameBase g)).mul
      ((continuous_apply _).comp u.property.derivative.continuous_framed)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  rw [integral_finsetSum _ (fun i _ => hL i)]
  simp_rw [scalar_oneForm_direction_green hRic f u]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hR i)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with e
  rw [oneFormDivergence_eq_frame, Finset.mul_sum]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The codifferential squares to zero in degrees two and one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.codifferentialBaseProbability
theorem smoothTwoFormCodifferential_gradient_orthogonal (hRic : RicciThree g)
    (u : smoothTwoForms o) (f : SmoothScalar (M := M)) :
    (∫ e, ∑ i, scalarGradient g f.val e i *
      covariantFieldFramed g (smoothTwoFormCodifferentialField u).val e ![i]
      ∂canonicalFrameMeasure g o) = 0 := by
  have ha := smoothOneFormExterior_adjoint hRic (smoothScalarDifferential g f) u
  rw [smoothScalarDifferential_closed] at ha
  simp only [smoothScalarDifferential_framed,
    ← smoothTwoFormCodifferentialField_component] at ha
  exact ha.symm.trans (show smoothTwoFormL2Inner (0 : smoothTwoForms o) u = 0 by
    simp [smoothTwoFormL2Inner])

theorem smoothTwoFormCodifferential_divergence (hRic : RicciThree g)
    (u : smoothTwoForms o) :
    smoothOneFormDivergence g (smoothTwoFormCodifferentialField u) = 0 := by
  let f := smoothOneFormDivergence g (smoothTwoFormCodifferentialField u)
  apply smoothScalar_eq_zero_of_square_integral (o := o)
  have hA := scalar_oneForm_adjoint (o := o) hRic f (smoothTwoFormCodifferentialField u)
  have hG := smoothTwoFormCodifferential_gradient_orthogonal hRic u f
  rw [hG] at hA
  have hzero := neg_eq_zero.mp hA.symm
  change (∫ e, f.val e.base * f.val e.base ∂canonicalFrameMeasure g o) = 0 at hzero
  simpa only [pow_two] using hzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! The degree-one Hodge Laplacian is the actual dδ+δd operator.
Its symmetry and nonnegative energy follow from the geometric adjoints. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.oneFormHodge_probability
theorem smoothScalarDifferential_pairing (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) (u : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (smoothScalarDifferential g f) u =
      -(∫ x, f.val x * oneFormDivergence g u x ∂normalizedVolume g) := by
  have hi : Integrable (fun x => f.val x * oneFormDivergence g u x) (normalizedVolume g) :=
    (f.property.continuous.mul (oneFormDivergence_smooth u).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [← canonicalFrameMeasure_integral_base g o _ hi]
  unfold smoothOneFormL2Pairing
  simp_rw [smoothScalarDifferential_framed]
  exact scalar_oneForm_adjoint hRic f u

theorem smoothTwoFormCodifferential_pairing (hRic : RicciThree g)
    (u : smoothTwoForms o) (v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (smoothTwoFormCodifferentialField u) v =
      smoothTwoFormL2Inner u (smoothOneFormExterior (o := o) v) := by
  rw [smoothOneFormL2Pairing_comm, smoothTwoFormL2Inner_comm,
    smoothOneFormExterior_adjoint hRic]
  simp only [smoothOneFormL2Pairing, smoothTwoFormCodifferentialField_component]

theorem smoothOneFormHodgeLaplacian_pairing (hRic : RicciThree g)
    (u v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (smoothOneFormHodgeLaplacian (o := o) u) v =
      smoothOneFormHodgeEnergy (o := o) u v := by
  rw [smoothOneFormHodgeLaplacian_apply, smoothOneFormL2Pairing_sub,
    smoothTwoFormCodifferential_pairing hRic, smoothScalarDifferential_pairing hRic]
  change _ - -_ = _ + _
  rw [sub_neg_eq_add]
  rfl

theorem smoothOneFormHodgeLaplacian_selfAdjoint (hRic : RicciThree g)
    (u v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) (smoothOneFormHodgeLaplacian (o := o) u) v =
      smoothOneFormL2Pairing (o := o) u (smoothOneFormHodgeLaplacian (o := o) v) := by
  rw [smoothOneFormHodgeLaplacian_pairing hRic, smoothOneFormL2Pairing_comm,
    smoothOneFormHodgeLaplacian_pairing hRic, smoothOneFormHodgeEnergy_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual codifferential extends continuously from the two-form H1
completion into the one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothH1Codifferential : SmoothH1TwoForm o →ₗ[ℝ] SmoothL2OneForm o where
  toFun u := ⟨smoothTwoFormCodifferentialField u⟩
  map_add' u v := by
    apply (smoothL2OneFormEquiv o).injective
    exact (smoothTwoFormCodifferentialLinear (o := o)).map_add u v
  map_smul' r u := by
    apply (smoothL2OneFormEquiv o).injective
    exact (smoothTwoFormCodifferentialLinear (o := o)).map_smul r u

theorem smoothH1Codifferential_norm_sq (u : SmoothH1TwoForm o) :
    ‖smoothH1Codifferential u‖ ^ 2 =
      twoFormCodiffPairing (u : smoothTwoForms o) (u : smoothTwoForms o) := by
  rw [← real_inner_self_eq_norm_sq, smoothOneForm_inner_eq]
  change smoothOneFormL2Pairing (o := o)
    (smoothTwoFormCodifferentialField (u : smoothTwoForms o))
    (smoothTwoFormCodifferentialField (u : smoothTwoForms o)) = _
  exact integral_congr_ae (Filter.Eventually.of_forall fun e =>
    Finset.sum_congr rfl fun k _ => congrArg₂ (· * ·)
      (smoothTwoFormCodifferentialField_component (u : smoothTwoForms o) e k)
      (smoothTwoFormCodifferentialField_component (u : smoothTwoForms o) e k))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exterior derivative from actual scalar H1 to actual one-form L2.
The extension is made along the dense range of smooth first jets. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_13
theorem smoothScalarFirstJet_injective
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    Function.Injective (smoothScalarFirstJet d) := by
  intro f h he
  apply smoothScalarValueL2_injective g o
  exact congrArg (fun u : ScalarJetL2 g (canonicalFrameMeasure g o) => u none) he

def scalarFirstJetRangeEquiv (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    SmoothScalar (M := M) ≃ₗ[ℝ] LinearMap.range (smoothScalarFirstJet d) :=
  LinearEquiv.ofInjective (smoothScalarFirstJet d) (smoothScalarFirstJet_injective d)

theorem scalarFirstJetRangeInclusion_dense
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    DenseRange (scalarFirstJetRangeInclusion d) := by
  change Dense (Set.range (scalarFirstJetRangeInclusion d))
  rw [Topology.IsInducing.subtypeVal.dense_iff]
  intro u
  apply closure_mono (s := Set.range (smoothScalarFirstJet d)) ?_ u.property
  rintro v ⟨a, rfl⟩
  exact ⟨scalarFirstJetRangeInclusion d (scalarFirstJetRangeEquiv d a),
    ⟨scalarFirstJetRangeEquiv d a, rfl⟩, rfl⟩

theorem scalarFirstJetRangeInclusion_equiv
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f : SmoothScalar (M := M)) :
    scalarFirstJetRangeInclusion d (scalarFirstJetRangeEquiv d f) = smoothScalarToH1 d f := rfl

theorem smoothScalarDifferential_dirichlet
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f h : SmoothScalar (M := M)) :
    smoothOneFormL2Pairing (o := o) (smoothScalarDifferential g f)
      (smoothScalarDifferential g h) = smoothScalarDirichlet d f h := by
  rw [smoothScalarDirichlet_eq_integral]
  unfold smoothOneFormL2Pairing
  simp only [smoothScalarDifferential_framed]

theorem smoothScalarDifferential_norm_le
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f : SmoothScalar (M := M)) :
    ‖(⟨smoothScalarDifferential g f⟩ : SmoothL2OneForm o)‖ ≤ ‖smoothScalarToH1 d f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, smoothOneForm_inner_eq,
    smoothScalarDifferential_dirichlet d, scalarH1_norm_sq]
  simp only [scalarH1Value_smooth, scalarH1Gradient_smooth]
  unfold smoothScalarDirichlet
  simp only [real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_left (sq_nonneg _)

def smoothScalarDifferentialL2 : SmoothScalar (M := M) →ₗ[ℝ] SmoothL2OneForm o where
  toFun f := ⟨smoothScalarDifferential g f⟩
  map_add' f h := by
    apply (smoothL2OneFormEquiv o).injective
    exact (smoothScalarDifferentialLinear g).map_add f h
  map_smul' r f := by
    apply (smoothL2OneFormEquiv o).injective
    exact (smoothScalarDifferentialLinear g).map_smul r f

def scalarFirstJetDifferential (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    LinearMap.range (smoothScalarFirstJet d) →ₗ[ℝ] SmoothL2OneForm o :=
  smoothScalarDifferentialL2.comp (scalarFirstJetRangeEquiv d).symm.toLinearMap

theorem scalarFirstJetDifferential_equiv
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f : SmoothScalar (M := M)) :
    scalarFirstJetDifferential d (scalarFirstJetRangeEquiv d f) =
      (⟨smoothScalarDifferential g f⟩ : SmoothL2OneForm o) := by
  change smoothScalarDifferentialL2
    ((scalarFirstJetRangeEquiv d).symm (scalarFirstJetRangeEquiv d f)) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

theorem scalarFirstJetDifferential_norm_le
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : LinearMap.range (smoothScalarFirstJet d)) : ‖scalarFirstJetDifferential d u‖ ≤ ‖u‖ := by
  obtain ⟨f, rfl⟩ := (scalarFirstJetRangeEquiv d).surjective u
  rw [scalarFirstJetDifferential_equiv]
  exact smoothScalarDifferential_norm_le d f

def scalarFirstJetDifferentialCLM (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    LinearMap.range (smoothScalarFirstJet d) →L[ℝ] OneFormL2 o :=
  smoothOneFormToL2.toContinuousLinearMap.comp
    ((scalarFirstJetDifferential d).mkContinuous 1
      (fun u => by simpa only [one_mul] using scalarFirstJetDifferential_norm_le d u))

def scalarH1Differential (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    scalarH1 d →L[ℝ] OneFormL2 o :=
  (scalarFirstJetDifferentialCLM d).extend (scalarFirstJetRangeInclusion d).toContinuousLinearMap

theorem scalarH1Differential_range
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : LinearMap.range (smoothScalarFirstJet d)) :
    scalarH1Differential d (scalarFirstJetRangeInclusion d u) =
      scalarFirstJetDifferentialCLM d u := by
  exact ContinuousLinearMap.extend_eq (scalarFirstJetDifferentialCLM d)
    (e := (scalarFirstJetRangeInclusion d).toContinuousLinearMap)
    (scalarFirstJetRangeInclusion_dense d)
    (scalarFirstJetRangeInclusion d).isometry.isUniformInducing u

theorem scalarH1Differential_smooth
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (f : SmoothScalar (M := M)) :
    scalarH1Differential d (smoothScalarToH1 d f) =
      smoothOneFormToL2 (⟨smoothScalarDifferential g f⟩ : SmoothL2OneForm o) := by
  calc
    _ = scalarH1Differential d
        (scalarFirstJetRangeInclusion d (scalarFirstJetRangeEquiv d f)) :=
      congrArg (scalarH1Differential d) (scalarFirstJetRangeInclusion_equiv d f).symm
    _ = scalarFirstJetDifferentialCLM d (scalarFirstJetRangeEquiv d f) :=
      scalarH1Differential_range d _
    _ = _ := congrArg smoothOneFormToL2 (scalarFirstJetDifferential_equiv d f)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive Ricci curvature eliminates the kernel of the actual
degree-one Hodge Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.oneFormKernel_probability
theorem smoothOneFormHodgeLaplacian_eq_zero (hRic : RicciThree g)
    (u : smoothCovariantFields M 1) (hu : smoothOneFormHodgeLaplacian (o := o) u = 0) :
    u = 0 := by
  have he := smoothOneFormHodgeLaplacian_pairing (o := o) hRic u u
  rw [hu] at he
  have hz : smoothOneFormL2Pairing (o := o) 0 u = 0 := by
    simpa only [zero_smul, zero_mul] using smoothOneFormL2Pairing_smul (o := o) 0 u u
  rw [hz] at he
  have hdiv : 0 ≤ ∫ x, oneFormDivergence g u x * oneFormDivergence g u x
      ∂normalizedVolume g := integral_nonneg fun _ => mul_self_nonneg _
  have hnonneg := smoothTwoFormL2Inner_nonneg (smoothOneFormExterior (o := o) u)
  have hdu : smoothOneFormExterior (o := o) u = 0 := by
    apply smoothTwoFormL2Inner_definite
    change 0 = _ + _ at he
    linarith
  have hbase : (∫ x, oneFormDivergence g u x ^ 2 ∂normalizedVolume g) = 0 := by
    change 0 = _ + _ at he
    simp only [pow_two]
    linarith
  let f := smoothOneFormDivergence g u
  have hi : Integrable (fun x => f.val x ^ 2) (normalizedVolume g) :=
    (f.property.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hf : f = 0 := smoothScalar_eq_zero_of_square_integral (o := o) f
    ((canonicalFrameMeasure_integral_base g o _ hi).trans hbase)
  apply oneForm_harmonic_eq_zero hRic u hdu
  intro e
  rw [← oneFormDivergence_eq_frame]
  exact congrArg (fun v : SmoothScalar (M := M) => v.val e.base) hf

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Closed two-forms are orthogonal to coexact forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_closed_codiff_hodge (u : smoothTwoForms o)
    (hu : smoothTwoFormExterior u = 0) :
    smoothTwoFormCodifferential (smoothTwoFormHodge o u) = 0 := by
  have hd (e : FrameBundle g) (i j k : Fin 4) : smoothTwoFormExterior u e i j k = 0 :=
    congrFun (congrFun (congrFun (congrFun hu e) i) j) k
  funext e k
  have h := twoFormDeRhamDensity_hodge u e.base
  rw [twoFormDeRhamDensity_eq_frame, twoFormCodiffDensity_eq_frame u e,
    twoFormCodiffDensity_eq_frame (smoothTwoFormHodge o u) e,
    twoFormCodiffTensor_squareNorm, twoFormCodiffTensor_squareNorm] at h
  change (1 / 6 : ℝ) * (∑ i, ∑ j, ∑ k, smoothTwoFormExterior u e i j k ^ 2) +
      (∑ k, smoothTwoFormCodifferential u e k ^ 2) =
      (∑ k, smoothTwoFormCodifferential u e k ^ 2) +
      (∑ k, smoothTwoFormCodifferential (smoothTwoFormHodge o u) e k ^ 2) at h
  simp only [hd, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero,
    mul_zero, zero_add] at h
  have hs : (∑ k, smoothTwoFormCodifferential (smoothTwoFormHodge o u) e k ^ 2) = 0 := by
    linarith only [h]
  have hk : smoothTwoFormCodifferential (smoothTwoFormHodge o u) e k ^ 2 ≤
      ∑ j, smoothTwoFormCodifferential (smoothTwoFormHodge o u) e j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  rw [hs] at hk
  exact (sq_eq_zero_iff.mp (le_antisymm hk (sq_nonneg _)))

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem smoothOneForm_coexact_orthogonal_closed (hRic : RicciThree g)
    (a : smoothCovariantFields (M := M) 1) (v : smoothTwoForms o)
    (hv : smoothTwoFormExterior v = 0) :
    smoothTwoFormL2Inner (smoothTwoFormHodge o (smoothOneFormExterior a)) v = 0 := by
  rw [smoothTwoFormL2Inner_hodge_left, smoothOneFormExterior_adjoint hRic]
  have hz := smoothTwoForm_closed_codiff_hodge v hv
  simp only [hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero, integral_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Closedness is exactly vanishing of the Hodge-dual codifferential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_closed_iff_codifferential_hodge (u : smoothTwoForms o) :
    smoothTwoFormExterior u = 0 ↔
      smoothTwoFormCodifferentialField (smoothTwoFormHodge o u) = 0 := by
  rw [smoothTwoFormCodifferentialField_eq_zero_iff]
  constructor
  · exact smoothTwoForm_closed_codiff_hodge u
  · intro hu
    have hz (e : FrameBundle g) (k : Fin 4) :
        smoothTwoFormCodifferential (smoothTwoFormHodge o u) e k = 0 :=
      congrFun (congrFun hu e) k
    funext e i j k
    have h := twoFormDeRhamDensity_hodge u e.base
    rw [twoFormDeRhamDensity_eq_frame, twoFormCodiffDensity_eq_frame u e,
      twoFormCodiffDensity_eq_frame (smoothTwoFormHodge o u) e,
      twoFormCodiffTensor_squareNorm, twoFormCodiffTensor_squareNorm] at h
    change (1 / 6 : ℝ) * (∑ i, ∑ j, ∑ k, smoothTwoFormExterior u e i j k ^ 2) +
        (∑ k, smoothTwoFormCodifferential u e k ^ 2) =
        (∑ k, smoothTwoFormCodifferential u e k ^ 2) +
        (∑ k, smoothTwoFormCodifferential (smoothTwoFormHodge o u) e k ^ 2) at h
    simp only [hz, zero_pow (by norm_num : 2 ≠ 0), Finset.sum_const_zero, add_zero] at h
    have hs : (∑ i, ∑ j, ∑ k, smoothTwoFormExterior u e i j k ^ 2) = 0 := by
      linarith only [h]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a (_ : a ∈ Finset.univ) => show 0 ≤ ∑ b, ∑ c,
        smoothTwoFormExterior u e a b c ^ 2 by positivity)).mp hs i (Finset.mem_univ i)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b (_ : b ∈ Finset.univ) => show 0 ≤ ∑ c,
        smoothTwoFormExterior u e i b c ^ 2 by positivity)).mp hi j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun c (_ : c ∈ Finset.univ) => sq_nonneg (smoothTwoFormExterior u e i j c))).mp
      hj k (Finset.mem_univ k))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual degree-zero, one and two Hodge operators commute with
the exterior derivative and its metric adjoint. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneForm_eq_of_pairings (u v : smoothCovariantFields M 1)
    (h : ∀ w, smoothOneFormL2Pairing (o := o) u w = smoothOneFormL2Pairing (o := o) v w) :
    u = v := by
  apply sub_eq_zero.mp
  apply smoothOneFormL2Pairing_definite (o := o)
  rw [smoothOneFormL2Pairing_sub, h, sub_self]

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothOneFormDivergence_differential (f : SmoothScalar (M := M)) :
    smoothOneFormDivergence g (smoothScalarDifferential g f) = smoothScalarLaplacian g f := by
  apply Subtype.ext
  funext x
  exact oneFormDivergence_differential f (frameAt g x)

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothOneFormHodgeLaplacian_differential (f : SmoothScalar (M := M)) :
    smoothOneFormHodgeLaplacian (o := o) (smoothScalarDifferential g f) =
      -smoothScalarDifferential g (smoothScalarLaplacian g f) := by
  rw [smoothOneFormHodgeLaplacian_apply, smoothScalarDifferential_closed,
    show smoothTwoFormCodifferentialField (0 : smoothTwoForms o) = 0 from
      (smoothTwoFormCodifferentialLinear (o := o)).map_zero,
    zero_sub, smoothOneFormDivergence_differential]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HeatKernels10
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Actual exact and coexact smooth one-form eigensections and their
orthogonality. The coexact eigenspaces are finite images of the proved
two-form eigenspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothOneFormL2Linear_injective : Function.Injective (smoothOneFormL2Linear (o := o)) := by
  intro u v h
  exact congrArg SmoothL2OneForm.toSmooth (smoothOneFormToL2_injective h)

theorem smoothOneFormL2Linear_inner (u v : smoothCovariantFields M 1) :
    inner ℝ (smoothOneFormL2Linear (o := o) u) (smoothOneFormL2Linear (o := o) v) =
      smoothOneFormL2Pairing (o := o) u v := smoothOneFormToL2_inner _ _

theorem smoothOneFormL2Pairing_smul_right (r : ℝ) (u v : smoothCovariantFields M 1) :
    smoothOneFormL2Pairing (o := o) u (r • v) = r * smoothOneFormL2Pairing (o := o) u v := by
  rw [smoothOneFormL2Pairing_comm, smoothOneFormL2Pairing_smul,
    smoothOneFormL2Pairing_comm v u]

theorem oneForm_exact_coexact_orthogonal (hRic : RicciThree g)
    (f : SmoothScalar (M := M)) (u : smoothTwoForms o) :
    inner ℝ (smoothOneFormL2Linear (o := o) (smoothScalarDifferential g f))
      (smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u)) = 0 := by
  rw [smoothOneFormL2Linear_inner, smoothScalarDifferential_pairing hRic]
  have hz := smoothTwoFormCodifferential_divergence hRic u
  have hpoint (x : M) : oneFormDivergence g (smoothTwoFormCodifferentialField u) x = 0 :=
    congrArg (fun a : SmoothScalar (M := M) => a.val x) hz
  simp only [hpoint, mul_zero, integral_zero, neg_zero]

theorem smoothOneForm_eigen_orthogonal (hRic : RicciThree g)
    (u v : smoothCovariantFields M 1) (κ l : ℝ)
    (hu : smoothOneFormHodgeLaplacian (o := o) u = κ • u)
    (hv : smoothOneFormHodgeLaplacian (o := o) v = l • v) (hne : κ ≠ l) :
    inner ℝ (smoothOneFormL2Linear (o := o) u) (smoothOneFormL2Linear (o := o) v) = 0 := by
  rw [smoothOneFormL2Linear_inner]
  have he := smoothOneFormHodgeLaplacian_selfAdjoint (o := o) hRic u v
  rw [hu, hv, smoothOneFormL2Pairing_smul, smoothOneFormL2Pairing_smul_right] at he
  exact (mul_eq_zero.mp (show (κ - l) * smoothOneFormL2Pairing (o := o) u v = 0 by
    nlinarith only [he])).resolve_left (sub_ne_zero.mpr hne)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Banach space obtained by uniformly completing genuine smooth one-forms.
Frame norms descend to the base, so its L2 realization remains injective. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_17
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureFrameBundleCanonicalFrameMeasure
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureNormalizedVolume_2
def smoothOneFormContinuousLinear : smoothCovariantFields M 1 →ₗ[ℝ] C(FrameBundle g, FourSpace) where
  toFun := smoothOneFormEuclideanValue
  map_add' u v := by
    ext e i
    exact congrFun (covariantFieldFramed_add (g := g) u.val v.val e) ![i]
  map_smul' r u := by
    ext e i
    exact congrFun (covariantFieldFramed_smul (g := g) r u.val e) ![i]

def oneFormContinuousSubspace (g : SmoothMetric M) : Submodule ℝ C(FrameBundle g, FourSpace) :=
  (smoothOneFormContinuousLinear (g := g)).range.topologicalClosure

abbrev OneFormC0 (g : SmoothMetric M) := ↥(oneFormContinuousSubspace g)

instance oneFormC0_complete : CompleteSpace (OneFormC0 g) :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem smoothOneFormEuclideanValue_norm_base (u : smoothCovariantFields M 1) (e f : FrameBundle g)
    (hef : e.base = f.base) : ‖smoothOneFormEuclideanValue (g := g) u e‖ = ‖smoothOneFormEuclideanValue (g := g) u f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin 4, covariantFieldFramed g u.val e ![i] ^ 2) =
    ∑ i : Fin 4, covariantFieldFramed g u.val f ![i] ^ 2
  rw [← oneForm_squareNorm, ← oneForm_squareNorm,
    ← covariantFieldNormSq_eq_frame u.val e, ← covariantFieldNormSq_eq_frame u.val f, hef]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem oneFormC0_norm_base (u : OneFormC0 g) (e f : FrameBundle g) (hef : e.base = f.base) :
    ‖u.val e‖ = ‖u.val f‖ := by
  have hc : IsClosed {F : C(FrameBundle g, FourSpace) | ‖F e‖ = ‖F f‖} :=
    isClosed_eq ((continuous_eval_const e).norm) ((continuous_eval_const f).norm)
  apply hc.closure_subset_iff.mpr _ u.property
  rintro _ ⟨v, rfl⟩
  exact smoothOneFormEuclideanValue_norm_base v e f hef

def oneFormC0BaseNorm (u : OneFormC0 g) (x : M) : ℝ := ‖u.val (frameAt g x)‖

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem oneFormC0BaseNorm_frame (u : OneFormC0 g) (e : FrameBundle g) :
    oneFormC0BaseNorm u e.base = ‖u.val e‖ :=
  oneFormC0_norm_base u (frameAt g e.base) e rfl

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem oneFormC0BaseNorm_continuous (u : OneFormC0 g) : Continuous (oneFormC0BaseNorm u) := by
  have hq := Topology.IsQuotientMap.of_surjective_continuous
    (frameBase_surjective g) (continuous_frameBase g)
  apply hq.continuous_iff.mpr
  change Continuous (fun e : FrameBundle g => oneFormC0BaseNorm u e.base)
  simp_rw [oneFormC0BaseNorm_frame]
  exact u.val.continuous.norm

def oneFormC0ToFrameLp : OneFormC0 g →L[ℝ] Lp FourSpace 2 (canonicalFrameMeasure g o) :=
  (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ).comp (oneFormContinuousSubspace g).subtypeL

theorem oneFormC0ToFrameLp_norm_sq (u : OneFormC0 g) :
    ‖oneFormC0ToFrameLp (o := o) u‖ ^ 2 =
      ∫ x, oneFormC0BaseNorm u x ^ 2 ∂normalizedVolume g := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have he := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) u.val
  calc
    _ = ∫ e, ‖u.val e‖ ^ 2 ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [he] with e he
      change (oneFormC0ToFrameLp (o := o) u : FrameBundle g → FourSpace) e = _ at he
      rw [he, real_inner_self_eq_norm_sq]
    _ = ∫ e, oneFormC0BaseNorm u e.base ^ 2 ∂canonicalFrameMeasure g o := by
      simp only [oneFormC0BaseNorm_frame]
    _ = _ := canonicalFrameMeasure_integral_base g o _
      (((oneFormC0BaseNorm_continuous u).pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))

theorem oneFormC0ToFrameLp_injective : Function.Injective (oneFormC0ToFrameLp (g := g) (o := o)) := by
  suffices hz : ∀ u : OneFormC0 g, oneFormC0ToFrameLp (o := o) u = 0 → u = 0 by
    intro u v h
    exact sub_eq_zero.mp (hz (u - v) ((map_sub (oneFormC0ToFrameLp (o := o)) u v).trans (sub_eq_zero.mpr h)))
  intro u hu
  have hi : (∫ x, oneFormC0BaseNorm u x ^ 2 ∂normalizedVolume g) = 0 := by
    rw [← oneFormC0ToFrameLp_norm_sq (o := o), hu, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hc := (oneFormC0BaseNorm_continuous u).pow 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (oneFormC0BaseNorm u x))
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp hi
  let := normalizedVolume_isOpenPosMeasure g
  have he : (fun x => oneFormC0BaseNorm u x ^ 2) = fun _ => 0 :=
    Measure.eq_of_ae_eq hae hc continuous_const
  apply Subtype.ext
  apply ContinuousMap.ext
  intro e
  apply norm_eq_zero.mp
  have hb := congrFun he e.base
  rw [oneFormC0BaseNorm_frame] at hb
  exact (sq_eq_zero_iff).mp hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! Additivity of the actual normal amplitude realization, needed to
retain cancellation in the heat residual before estimating its norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCoordinates_add (a b : FourSpace → FourSpace) :
    heatNormalOneCoordinates D (a + b) =
      heatNormalOneCoordinates D a + heatNormalOneCoordinates D b := by
  funext x v
  change frameTensor (D.point x).2⁻¹ (fun q => (a x + b x) (q 0)) v = _
  have he : (fun q : Fin 1 → Fin 4 => (a x + b x) (q 0)) =
      (fun q => a x (q 0)) + (fun q => b x (q 0)) := rfl
  rw [he, frameTensor_add]
  rfl

omit [T3Space M] [CompactSpace M] in
theorem heatNormalOneFrameLift_add (C : OpenPartialHomeomorph FourSpace M)
    (T U : FourSpace → CovariantCoordinates 1) :
    heatNormalOneFrameLift g c C (T + U) =
      heatNormalOneFrameLift g c C T + heatNormalOneFrameLift g c C U := by
  classical
  funext f v
  by_cases hf : f.base ∈ C.target
  · simp only [heatNormalOneFrameLift, ite_eq_left hf, Pi.add_apply, frameTensor_add]
  · simp only [heatNormalOneFrameLift, ite_eq_right hf, Pi.add_apply, Pi.zero_apply, add_zero]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem heatNormalOneAmplitudeL2_add
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a b : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hca : HasCompactSupport a) (hcb : HasCompactSupport b)
    (hsa : tsupport a ⊆ C.source) (hsb : tsupport b ⊆ C.source) :
    heatNormalOneAmplitudeL2 D C hCt hP hD (a + b) (ha.add hb) (hca.add hcb)
      ((tsupport_add a b).trans (union_subset hsa hsb)) =
      heatNormalOneAmplitudeL2 D C hCt hP hD a ha hca hsa +
        heatNormalOneAmplitudeL2 D C hCt hP hD b hb hcb hsb := by
  have hT : heatNormalOneAmplitude D C hCt hP hD (a + b) (ha.add hb) (hca.add hcb)
      ((tsupport_add a b).trans (union_subset hsa hsb)) =
      heatNormalOneAmplitude D C hCt hP hD a ha hca hsa +
        heatNormalOneAmplitude D C hCt hP hD b hb hcb hsb := by
    ext f v
    change heatNormalOneFrameLift g c C (heatNormalOneCoordinates D (a + b)) f ![v] = _
    rw [heatNormalOneCoordinates_add, heatNormalOneFrameLift_add]
    rfl
  change oneFormFromContinuous _ = oneFormFromContinuous _ + oneFormFromContinuous _
  rw [hT, map_add]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Jointly continuous compact normal amplitudes give continuous curves
in the global one-form L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

local instance instCompactSpaceFrameBundle_20_r242dcf_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
theorem heatNormalOneAmplitudeL2_continuous_family
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (A : ℝ → FourSpace → FourSpace) (ha : ∀ t, ContDiff ℝ 2 (A t))
    (hc : ∀ t, HasCompactSupport (A t)) (hs : ∀ t, tsupport (A t) ⊆ C.source)
    (hA : ContinuousOn (fun z : ℝ × FourSpace => A z.1 z.2) (Ioi 0 ×ˢ C.source))
    (K : Set FourSpace) (hK : IsCompact K) (hKC : K ⊆ C.source)
    (hsK : ∀ t > 0, tsupport (A t) ⊆ K) :
    ContinuousOn (fun t => heatNormalOneAmplitudeL2 D C hCt hP hD (A t) (ha t) (hc t) (hs t)) (Ioi 0) := by
  have hcoord := heatNormalOneCoordinates_joint_continuous C hP hD A hA
  have hframe := heatNormalOneFrameLift_joint_continuous (g := g) C hCt
    (fun t => heatNormalOneCoordinates D (A t)) hcoord K hK hKC
    (fun t ht => (heatNormalOneCoordinates_support D (A t)).trans (hsK t ht))
  have hTF : ContinuousOn (fun z : ℝ × FrameBundle g =>
      (WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D (A z.1)) z.2 ![i])
        : FourSpace)) (Ioi 0 ×ˢ univ) :=
    by
    apply (PiLp.continuous_toLp 2 _).comp_continuousOn
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply ![i]).comp_continuousOn hframe
  have hcurve : ContinuousOn (fun t => heatNormalOneAmplitude D C hCt hP hD
      (A t) (ha t) (hc t) (hs t)) (Ioi 0) :=
    ContinuousMap.continuousOn_of_continuousOn_uncurry _ hTF
  exact oneFormFromContinuous.continuous.comp_continuousOn hcurve

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact normal one-form parametrix columns and their actual time derivatives. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalOneTimeColumn (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 4) (x : FourSpace) : FourSpace :=
  WithLp.toLp 2 (fun k => χ x * fourHeatGaussianPolynomialTime
    (fun m y => E.amplitude m y k l) t x)

theorem heatNormalOneTimeColumn_component (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (l k : Fin 4) (x : FourSpace) :
    heatNormalOneTimeColumn E χ t l x k =
      deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t :=
  ((fourHeatGaussianPolynomial_hasDerivAt (fun m y => E.amplitude m y k l) t ht x).const_mul
    (χ x)).deriv.symm

theorem heatNormalOneTimeColumn_regular (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (t : ℝ) (l : Fin 4) :
    ContDiff ℝ 2 (heatNormalOneTimeColumn E χ t l) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  have hu (m : Fin 4) : ContDiff ℝ 2 (fun y => E.amplitude m y k l) :=
    (E.amplitude_regular m (by omega) k l).of_le (by norm_num)
  have hQ : ContDiff ℝ 2 (fun x => fourHeatPolynomialTime (fun m y => E.amplitude m y k l) t x) :=
    ((hu 1).add ((contDiff_const (c := 2 * t)).mul (hu 2))).add
      ((contDiff_const (c := 3 * t ^ 2)).mul (hu 3))
  have hF : ContDiff ℝ 2 (fourHeatGaussianTimeFactor t) :=
    ((contDiff_norm_sq ℝ).div_const (4 * t ^ 2)).sub contDiff_const
  have hG : ContDiff ℝ 2 (fourHeatGaussian t) := (fourHeatGaussian_smooth t).of_le (by norm_num)
  exact hχ.mul (((hF.mul hG).mul (fourHeatPolynomial_contDiff _ hu t)).add (hG.mul hQ))

theorem heatNormalOneTimeColumn_support (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 4) :
    tsupport (heatNormalOneTimeColumn E χ t l) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have hχ : χ x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  apply WithLp.ofLp_injective 2
  funext k
  simp only [heatNormalOneTimeColumn, WithLp.ofLp_toLp, hχ, zero_mul, WithLp.ofLp_zero,
    Pi.zero_apply]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalOneGlobalTimeColumn (E : HeatNormalOneExtension D)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatNormalOneAmplitudeL2 D C hCt hP hD (heatNormalOneTimeColumn E χ t l)
    (heatNormalOneTimeColumn_regular E χ hχ t l)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneTimeColumn_support E χ t l))
    ((heatNormalOneTimeColumn_support E χ t l).trans hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative and Hodge image are combined before estimation,
so the actual Gaussian transport cancellations are retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalOneResidualColumn (E : HeatNormalOneExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 4) : FourSpace → FourSpace :=
  heatNormalOneTimeColumn E χ t l + heatNormalOneOperatorAmplitude E (heatNormalOneCutoffColumn E χ t l)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative of the actual compact normal kernel under one
scalar pairing; only the cutoff-weighted test must be continuous. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCutoffParametrix_pairing_deriv (E : HeatNormalOneExtension D)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hc : HasCompactSupport χ) (t : ℝ) (ht : 0 < t) (k l : Fin 4) :
    HasDerivAt (fun s => ∫ x, heatNormalOneCutoffParametrix E χ s x k l * f x)
      (∫ x, deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t * f x) t := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => E.amplitude m x k l
  have h := fourHeat_compact_polynomial_pairing_deriv (fun x => χ x * f x) hχf hc.mul_right
    u (fun m => (E.amplitude_regular m (by omega) k l).continuous) t ht
  have hfun : (fun s => ∫ x, (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x)) =
      fun s => ∫ x, heatNormalOneCutoffParametrix E χ s x k l * f x := by
    funext s
    apply integral_congr_ae
    filter_upwards [] with x
    change (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x) =
      (χ x * (fourHeatGaussian s x * fourHeatPolynomial u s x)) * f x
    ring
  have hval : (∫ x, (χ x * f x) * fourHeatGaussianPolynomialTime u t x) =
      ∫ x, deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t * f x := by
    apply integral_congr_ae
    filter_upwards [] with x
    have hd := (fourHeatGaussianPolynomial_hasDerivAt u t ht x).const_mul (χ x)
    change HasDerivAt (fun s => heatNormalOneCutoffParametrix E χ s x k l)
      (χ x * fourHeatGaussianPolynomialTime u t x) t at hd
    rw [hd.deriv]
    ring
  rwa [hfun, hval] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second-order image of a compact C4 normal amplitude is an actual
compact C2 amplitude, so it can be realized in the same global L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCutoffColumn_regular_four (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (t : ℝ) (l : Fin 6) :
    ContDiff ℝ 4 (heatNormalCutoffColumn E χ t l) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  have hP := (((E.amplitude_regular 0 (by omega) k l).add
    ((contDiff_const (c := t)).mul (E.amplitude_regular 1 (by omega) k l))).add
    ((contDiff_const (c := t ^ 2)).mul (E.amplitude_regular 2 (by omega) k l))).add
    ((contDiff_const (c := t ^ 3)).mul (E.amplitude_regular 3 (by omega) k l))
  exact hχ.mul (((fourHeatGaussian_smooth t).of_le (by norm_num)).mul hP)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual time derivative column is a compact C2 normal amplitude
and therefore determines a section of the same global L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalTimeColumn (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 6) (x : FourSpace) : TwoFormFour :=
  WithLp.toLp 2 (fun k => χ x * fourHeatGaussianPolynomialTime
    (fun m y => E.amplitude m y k l) t x)

theorem heatNormalTimeColumn_regular (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (t : ℝ) (l : Fin 6) :
    ContDiff ℝ 2 (heatNormalTimeColumn E χ t l) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  have hu (m : Fin 4) : ContDiff ℝ 2 (fun y => E.amplitude m y k l) :=
    (E.amplitude_regular m (by omega) k l).of_le (by norm_num)
  have hQ : ContDiff ℝ 2 (fun x => fourHeatPolynomialTime (fun m y => E.amplitude m y k l) t x) :=
    ((hu 1).add ((contDiff_const (c := 2 * t)).mul (hu 2))).add
      ((contDiff_const (c := 3 * t ^ 2)).mul (hu 3))
  have hF : ContDiff ℝ 2 (fourHeatGaussianTimeFactor t) :=
    ((contDiff_norm_sq ℝ).div_const (4 * t ^ 2)).sub contDiff_const
  have hG : ContDiff ℝ 2 (fourHeatGaussian t) := (fourHeatGaussian_smooth t).of_le (by norm_num)
  exact hχ.mul (((hF.mul hG).mul (fourHeatPolynomial_contDiff _ hu t)).add (hG.mul hQ))

theorem heatNormalTimeColumn_support (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) :
    tsupport (heatNormalTimeColumn E χ t l) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  contrapose! hx
  have hχ : χ x = 0 := Function.notMem_support.mp hx
  apply Function.notMem_support.mpr
  apply WithLp.ofLp_injective 2
  funext k
  simp only [heatNormalTimeColumn, WithLp.ofLp_toLp, hχ, zero_mul, WithLp.ofLp_zero,
    Pi.zero_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint positive-time regularity of the actual cutoff normal kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalCutoffParametrix_joint_contDiffAt (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (z : ℝ × FourSpace) (ht : 0 < z.1)
    (k l : Fin 6) :
    ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => heatNormalCutoffParametrix E χ w.1 w.2 k l) z := by
  have hu (m : Fin 4) : ContDiff ℝ 2 (fun x => E.amplitude m x k l) :=
    (E.amplitude_regular m (by omega) k l).of_le (by norm_num)
  exact ((hχ.comp contDiff_snd).contDiffAt).mul
    ((fourHeatGaussian_joint_contDiffAt z ht).mul
      (fourHeatPolynomial_joint_contDiff _ hu).contDiffAt)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The time derivative and Hodge image are combined before estimation,
so the actual Gaussian transport cancellations are retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalResidualColumn (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ)
    (t : ℝ) (l : Fin 6) : FourSpace → TwoFormFour :=
  heatNormalTimeColumn E χ t l + heatNormalOperatorAmplitude E (heatNormalCutoffColumn E χ t l)

end
end PositiveEinsteinFour.Geometry
end


section

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCutoffParametrix_joint_contDiffAt (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (z : ℝ × FourSpace) (ht : 0 < z.1)
    (k l : Fin 4) :
    ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => heatNormalOneCutoffParametrix E χ w.1 w.2 k l) z := by
  have hu (m : Fin 4) : ContDiff ℝ 2 (fun x => E.amplitude m x k l) :=
    (E.amplitude_regular m (by omega) k l).of_le (by norm_num)
  exact ((hχ.comp contDiff_snd).contDiffAt).mul
    ((fourHeatGaussian_joint_contDiffAt z ht).mul
      (fourHeatPolynomial_joint_contDiff _ hu).contDiffAt)

theorem heatNormalOneTimeColumn_joint_continuousOn (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 4) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalOneTimeColumn E χ z.1 l z.2)
      (Ioi 0 ×ˢ univ) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro k
  exact (hχ.comp continuous_snd).continuousOn.mul
    (fourHeatGaussianPolynomialTime_continuousOn _
      (fun m => (E.amplitude_regular m (by omega) k l).continuous))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact Gaussian-free column and its uniform density-weighted bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOnePolynomialColumn_continuous (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 4) :
    Continuous (fun z : ℝ × FourSpace => heatNormalOnePolynomialColumn E χ z.1 l z.2) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro k
  exact (hχ.comp continuous_snd).mul
    (fourHeatPolynomial_joint_continuous _
      (fun m => (E.amplitude_regular m (by omega) k l).continuous))

theorem heatNormalOnePolynomialColumn_weight_bound (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ) (l : Fin 4) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      frameExponentialJacobian g o e x * ‖heatNormalOnePolynomialColumn E χ t l x‖ ^ 2 ≤ B := by
  let W := fun z : ℝ × FourSpace => frameExponentialJacobian g o e z.2 *
    ‖heatNormalOnePolynomialColumn E χ z.1 l z.2‖ ^ 2
  have hW : Continuous W := ((frameExponentialJacobian_continuous g o e).comp continuous_snd).mul
    ((heatNormalOnePolynomialColumn_continuous E χ hχ l).norm.pow 2)
  obtain ⟨B, hb⟩ := (isCompact_Icc.prod hc).bddAbove_image hW.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hb ⟨(t, x), ⟨ht, hx⟩, rfl⟩).trans (le_max_left _ _)
  · have hzero : heatNormalOnePolynomialColumn E χ t l x = 0 := by
      apply WithLp.ofLp_injective 2
      funext k
      change χ x * _ = 0
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
    rw [hzero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact le_max_right _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual compact kernel and its residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneOperatorColumn_joint_continuousOn (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (l : Fin 4) :
    ContinuousOn (fun z : ℝ × FourSpace =>
      heatNormalOneOperatorAmplitude E (heatNormalOneCutoffColumn E χ z.1 l) z.2)
      (Ioi 0 ×ˢ univ) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro k z hz
  exact (fourHeatOneOperator_joint_continuousAt E.base.a E.base.b E.B E.C
    (fun w k => heatNormalOneCutoffParametrix E χ w.1 w.2 k l) z
    (fun i j => (E.base.a_regular i j).continuous.continuousAt)
    (fun i => (E.base.b_regular i).continuous.continuousAt)
    (fun i k l => (E.B_regular i k l).continuous.continuousAt)
    (fun k l => (E.C_regular k l).continuous.continuousAt)
    (fun k => heatNormalOneCutoffParametrix_joint_contDiffAt E χ hχ z hz.1 k l) k).continuousWithinAt

theorem heatNormalOneResidualColumn_joint_continuousOn (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (l : Fin 4) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalOneResidualColumn E χ z.1 l z.2)
      (Ioi 0 ×ˢ univ) :=
  (heatNormalOneTimeColumn_joint_continuousOn E χ hχ.continuous l).add
    (heatNormalOneOperatorColumn_joint_continuousOn E χ hχ l)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Gaussian concentration gives the weighted square-integral growth t⁻². -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalOneCutoffColumn_square_integral_bound (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ) (l : Fin 4) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1,
      (∫ x, frameExponentialJacobian g o e x * ‖heatNormalOneCutoffColumn E χ t l x‖ ^ 2) ≤ C / t ^ 2 := by
  obtain ⟨B, hB, hb⟩ := heatNormalOnePolynomialColumn_weight_bound E χ hχ.continuous hc l
  refine ⟨B / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro t ht
  have hpt (x : FourSpace) : frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn E χ t l x‖ ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [heatNormalOneCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      _ = (frameExponentialJacobian g o e x * ‖heatNormalOnePolynomialColumn E χ t l x‖ ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb t ⟨ht.1.le, ht.2⟩ x) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hm : Continuous (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn E χ t l x‖ ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((heatNormalOneCutoffColumn_regular E χ (by exact hχ) t l).continuous.norm.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalOneCutoffColumn E χ t l x‖ ^ 2) :=
    hi.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hpt x)
  calc
    _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hpt
    _ = _ := by
      rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first signed coefficient is a joint C2 family, with a uniform
quadratic zero at every actual normal center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilySignedFirst (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (z : HeatRadialFrameSpace) : ℝ :=
  χ z.1 ^ 2 / E.U z * (twoFormHodgeMatrix * E.amplitude 1 z).trace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.signedFirst_family (N : HeatCommonNormalMember g o c E r e)
    (χ : FourSpace → ℝ) (hχs : tsupport χ ⊆ ball 0 r) (x : FourSpace) :
    N.extension.signedFirst χ x = heatFamilySignedFirst E χ (x, frameCoordinateState g c e) := by
  by_cases hx : x ∈ tsupport χ
  · have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.metric_pos x (hχs hx)))
    rw [← (N.actual x (hχs hx)).2.2.2.2, N.U_family] at hh
    unfold HeatNormalBundleExtension.signedFirst heatFamilySignedFirst
    rw [eq_inv_of_mul_eq_one_right hh, N.U_family, N.amplitude_family 1 (by omega)]
    dsimp only
    field_simp
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [HeatNormalBundleExtension.signedFirst, heatFamilySignedFirst,
      hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, zero_div]

end
end PositiveEinsteinFour.Geometry
end


section

/-! One genuine chart and cutoff for the actual one-form weak heat equation. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.oneTimeColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatNormalOneGlobalTimeColumn E P.chart P.in_chart P.point_regular P.inside_radius
    P.cutoff (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact P.cutoff_support t l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar differentiation commutes with the finite fiber traces in the
Euler combination of the first transport amplitudes. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem fourHeatLocalOperator_zero (a : Mat4) (b : Fin 4 → ℝ) (c : ℝ) (x : FourSpace) :
    fourHeatLocalOperator a b c (fun _ => 0) x = 0 := by
  simpa only [zero_mul] using fourHeatLocalOperator_const_mul a b c 0 (fun _ => 0) x

theorem fourHeatLocalOperator_finite_sum {ι : Type*} [Fintype ι]
    (a : Mat4) (b : Fin 4 → ℝ) (c : ℝ) (F : ι → FourSpace → ℝ)
    (hF : ∀ i, ContDiff ℝ 2 (F i)) (x : FourSpace) :
    fourHeatLocalOperator a b c (fun y => ∑ i, F i y) x =
      ∑ i, fourHeatLocalOperator a b c (F i) x := by
  classical
  have hsum (s : Finset ι) :
      fourHeatLocalOperator a b c (fun y => ∑ i ∈ s, F i y) x =
        ∑ i ∈ s, fourHeatLocalOperator a b c (F i) x := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using fourHeatLocalOperator_zero a b c x
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [fourHeatLocalOperator_add a b c (F i) (fun y => ∑ j ∈ s, F j y)
        (hF i) (ContDiff.sum (fun j _ => hF j)) x, ih]
  exact hsum Finset.univ

theorem heatOneMatrixScalarOperator_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : FourSpace → Mat4) (hA : ∀ k, ContDiff ℝ 2 (fun y => A y k k)) (x : FourSpace) :
    (heatOneMatrixScalarOperator a b A x).trace =
      fourHeatLocalOperator a b 0 (fun y => (A y).trace) x :=
  (fourHeatLocalOperator_finite_sum a b 0 (fun k y => A y k k) hA x).symm

theorem heatMatrixScalarOperator_trace (a : Mat4) (b : Fin 4 → ℝ)
    (A : FourSpace → HeatMat6) (hA : ∀ k, ContDiff ℝ 2 (fun y => A y k k)) (x : FourSpace) :
    (heatMatrixScalarOperator a b A x).trace =
      fourHeatLocalOperator a b 0 (fun y => (A y).trace) x :=
  (fourHeatLocalOperator_finite_sum a b 0 (fun k y => A y k k) hA x).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.eulerFirst_scalar_operator_zero
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) :
    2 * fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0
        (fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 1) 0 -
      2 * (heatOneMatrixScalarOperator (E.base.a 0) (E.base.b 0) (E.oneCompanion.amplitude 1) 0).trace +
      (heatMatrixScalarOperator (E.base.a 0) (E.base.b 0) (E.amplitude 1) 0).trace = 0 := by
  let F := fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 1
  let G := fun y => (E.oneCompanion.amplitude 1 y).trace
  let H := fun y => (E.amplitude 1 y).trace
  have hF : ContDiff ℝ 2 F := fourHeatCoefficient_contDiff 1 2 _ _ _ _
    (fun i j => (E.base.a_regular i j).of_le (by norm_num))
    (fun i => (E.base.b_regular i).of_le (by norm_num)) contDiff_const
    (E.base.U_regular.of_le (by norm_num)) (fun y => (E.base.U_pos y).ne')
  have hG : ContDiff ℝ 2 G := ContDiff.sum (fun k _ =>
    (E.oneCompanion.amplitude_regular 1 (by norm_num) k k).of_le (by norm_num))
  have hH : ContDiff ℝ 2 H := ContDiff.sum (fun k _ =>
    (E.amplitude_regular 1 (by norm_num) k k).of_le (by norm_num))
  have hz := fourHeatLocalOperator_germ (E.base.a 0) (E.base.b 0) 0
    (E.eulerFirstAmplitude_zero_near hRic)
  have heq : E.eulerFirstAmplitude = (fun y => 2 * F y + (-2) * G y + H y) := by
    funext y
    change 2 * F y - 2 * G y + H y = _
    ring
  rw [heq, fourHeatLocalOperator_add _ _ _ _ _ ((contDiff_const.mul hF).add (contDiff_const.mul hG)) hH,
    fourHeatLocalOperator_add _ _ _ _ _ (contDiff_const.mul hF) (contDiff_const.mul hG),
    fourHeatLocalOperator_const_mul, fourHeatLocalOperator_const_mul] at hz
  have hz0 : fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 (fun _ => 0) 0 = 0 := by
    exact fourHeatLocalOperator_zero _ _ _ _
  rw [hz0] at hz
  rw [heatOneMatrixScalarOperator_trace _ _ _
    (fun k => (E.oneCompanion.amplitude_regular 1 (by norm_num) k k).of_le (by norm_num)),
    heatMatrixScalarOperator_trace _ _ _
    (fun k => (E.amplitude_regular 1 (by norm_num) k k).of_le (by norm_num))]
  change 2 * fourHeatLocalOperator _ _ _ F 0 - 2 * fourHeatLocalOperator _ _ _ G 0 +
    fourHeatLocalOperator _ _ _ H 0 = 0
  linarith only [hz]

end
end PositiveEinsteinFour.Geometry
end


section

/-! All remaining signed polynomial coefficients have one compact bound
across the actual normal family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

def heatFamilySignedTail (E : HeatFamilySmoothCoefficients) (χ : FourSpace → ℝ)
    (t : ℝ) (z : HeatRadialFrameSpace) : ℝ :=
  (E.U z ^ 2)⁻¹ * χ z.1 ^ 2 *
    (2 * E.U z * (twoFormHodgeMatrix * E.amplitude 2 z).trace +
      heatSignedGram (E.amplitude 1 z) (E.amplitude 1 z) +
      t * (2 * E.U z * (twoFormHodgeMatrix * E.amplitude 3 z).trace +
        2 * heatSignedGram (E.amplitude 1 z) (E.amplitude 2 z)) +
      t ^ 2 * (2 * heatSignedGram (E.amplitude 1 z) (E.amplitude 3 z) +
        heatSignedGram (E.amplitude 2 z) (E.amplitude 2 z)) +
      t ^ 3 * (2 * heatSignedGram (E.amplitude 2 z) (E.amplitude 3 z)) +
      t ^ 4 * heatSignedGram (E.amplitude 3 z) (E.amplitude 3 z))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.signedTail_family (N : HeatCommonNormalMember g o c E r e)
    (χ : FourSpace → ℝ) (hχs : tsupport χ ⊆ ball 0 r) (t : ℝ) (x : FourSpace) :
    N.extension.signedTail χ t x = heatFamilySignedTail E χ t (x, frameCoordinateState g c e) := by
  by_cases hx : x ∈ tsupport χ
  · have hh := heatNormalLeadingAmplitude_normalization g o e x
      (Real.sqrt_pos.mpr (N.metric_pos x (hχs hx)))
    rw [← (N.actual x (hχs hx)).2.2.2.2, N.U_family] at hh
    unfold HeatNormalBundleExtension.signedTail heatFamilySignedTail
    rw [eq_inv_of_mul_eq_one_right hh, N.U_family, N.amplitude_family 1 (by omega),
      N.amplitude_family 2 (by omega), N.amplitude_family 3 (by omega)]
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [HeatNormalBundleExtension.signedTail, heatFamilySignedTail,
      hz, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! An actual quadratic integral bound for the global normal amplitude.
This keeps Gaussian spatial concentration, unlike the uniform norm bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_29
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instIsProbabilityMeasureNormalizedVolume_5
theorem heatNormalAmplitudeL2_norm_sq_le_integral
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) :
    ‖heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs‖ ^ 2 ≤
      2 * (normalizedChartFactor g).toReal *
        ∫ x, frameExponentialJacobian g o e x * ‖a x‖ ^ 2 := by
  let F := heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs
  let ψ := fun x => ‖a x‖ ^ 2
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have hz : a x = 0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    change ‖a x‖ ^ 2 = 0
    rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := (ha.continuous.norm.pow 2).continuousOn
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hs)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq (f : FrameBundle g) : ‖F f‖ ^ 2 = 2 * heatNormalScalarLift C ψ f.base := by
    by_cases hf : f.base ∈ C.target
    · rw [heatNormalAmplitudeTensor_norm_sq C hE hCt hP hD a ha hc hs f hf,
        heatNormalScalarLift_on_target C ψ hf]
    · have hz : F f = 0 := by
        change WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f) = _
        simp only [heatNormalFrameTensorLift, ite_eq_right hf]
        rfl
      rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
      simp only [heatNormalScalarLift, ite_eq_right hf, mul_zero]
  have hn := twoFormFromTensorL2_norm_le
    (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F)
  calc
    _ ≤ ‖ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F‖ ^ 2 := by
      change ‖twoFormFromTensorL2 (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F)‖ ^ 2 ≤ _
      nlinarith [norm_nonneg (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F),
        norm_nonneg (twoFormFromTensorL2 (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F))]
    _ = ∫ f, ‖F f‖ ^ 2 ∂canonicalFrameMeasure g o := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F] with f hf
      rw [hf, real_inner_self_eq_norm_sq]
    _ = 2 * ∫ y, heatNormalScalarLift C ψ y ∂normalizedVolume g := by
      simp_rw [heq]
      rw [integral_const_mul, canonicalFrameMeasure_integral_base g o _ hLi]
    _ = _ := by
      rw [heatNormalScalarLift_integral D C hE hCt hP hD ψ (hψs.trans hs)]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two coefficients that survive the signed Gaussian limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

omit [T3Space M] [CompactSpace M] in
theorem heat_actual_potential_symmetric (e : FrameBundle g) :
    (twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e))ᵀ =
      twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) := by
  have hR : ∀ i j k l, twoFormMetricCurvatureTensor g e ![k,l,i,j] =
      twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    intro i j k l
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame) i j k l
  simp only [twoFormPotentialMatrix, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, twoFormCurvatureMatrix_symmetric _ hR]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Cancellation of the differentiated first coefficient leaves the
actual quadratic Weitzenbock trace in the second Euler coefficient. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.second_amplitude_center (E : HeatNormalOneExtension D) :
    (2 : ℝ) • E.amplitude 2 0 =
      -heatOneMatrixScalarOperator (E.base.a 0) (E.base.b 0) (E.amplitude 1) 0 -
        ((3 : ℝ) • (1 : Mat4)) * E.amplitude 1 0 := by
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hB : E.B 0 = fun _ => 0 := by
    funext i
    exact (congrFun E.B_near.self_of_nhds i).trans (D.oneFirst_zero i)
  have hC : E.C 0 = (3 : ℝ) • (1 : Mat4) :=
    E.C_near.self_of_nhds.trans D.oneZero_center
  ext k l
  have hrec := fourHeatOneCoefficient_center 1 E.base.a E.base.b E.B E.C E.base.U
    (by rw [hU]; exact one_ne_zero) k l
  have hrec' : (2 : ℝ) * E.amplitude 2 0 k l =
      -fourHeatOneOperator (E.base.a 0) (E.base.b 0) (E.B 0) (E.C 0)
        (fun y q => E.amplitude 1 y q l) 0 k := by
    simpa only [HeatNormalOneExtension.amplitude, Nat.cast_one, one_add_one_eq_two] using hrec
  rw [hB, hC] at hrec'
  simp only [fourHeatOneOperator, fourHeatOneFirst, Matrix.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, fourHeatOneZero] at hrec'
  change 2 * E.amplitude 2 0 k l =
    -fourHeatLocalOperator (E.base.a 0) (E.base.b 0) 0 (fun y => E.amplitude 1 y k l) 0 -
      ∑ q, ((3 : ℝ) • (1 : Mat4)) k q * E.amplitude 1 0 q l
  linarith only [hrec']

def HeatNormalBundleExtension.eulerSecondAmplitude (E : HeatNormalBundleExtension D)
    (x : FourSpace) : ℝ :=
  2 * fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U 2 x -
    2 * (E.oneCompanion.amplitude 2 x).trace + (E.amplitude 2 x).trace

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual global parametrix column has L2 growth at most t⁻¹. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.oneColumn_growth (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (l : Fin 4) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.oneColumn E t l‖ ≤ C / t := by
  obtain ⟨B, hB, hb⟩ := heatNormalOneCutoffColumn_square_integral_bound E P.cutoff
    P.cutoff_regular P.cutoff_compact l
  let K := (normalizedChartFactor g).toReal * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro t ht
  have hn := heatNormalOneAmplitudeL2_norm_sq_integral P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius (heatNormalOneCutoffColumn E P.cutoff t l)
    ((heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l).of_le (by norm_num))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support E P.cutoff t l))
    ((heatNormalOneCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)
  have hn' : ‖P.oneColumn E t l‖ ^ 2 ≤ K / t ^ 2 := by
    exact (le_of_eq hn).trans ((mul_le_mul_of_nonneg_left (hb t ht) (by positivity)).trans_eq (by dsimp [K]; ring))
  have hs : (‖P.oneColumn E t l‖ * t) ^ 2 ≤ K := by
    calc
      _ = ‖P.oneColumn E t l‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (K / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      _ = K := by field_simp [ht.1.ne']
  apply (le_div_iff₀ ht.1).mpr
  nlinarith [sq_nonneg K, norm_nonneg (P.oneColumn E t l)]

theorem HeatNormalParametrixData.oneNormalizedColumn_growth (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (l : Fin 4) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.oneNormalizedColumn E t l‖ ≤ C / t := by
  obtain ⟨C, hC, hc⟩ := P.oneColumn_growth E l
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * C, by positivity, ?_⟩
  intro t ht
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.oneColumn E t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hc t ht) (norm_nonneg _)).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory11
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The finite alternating Gram polynomial for degrees zero, one and two. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators Matrix.Norms.Elementwise
noncomputable section

theorem heatEulerGram_add_left (A B C : HeatEulerFiber) :
    heatEulerGram (A + B) C = heatEulerGram A C + heatEulerGram B C := by
  simp only [heatEulerGram, Prod.fst_add, Prod.snd_add, Matrix.transpose_add,
    Matrix.add_mul, Matrix.trace_add]
  ring

theorem heatEulerGram_add_right (A B C : HeatEulerFiber) :
    heatEulerGram A (B + C) = heatEulerGram A B + heatEulerGram A C := by
  simp only [heatEulerGram, Prod.fst_add, Prod.snd_add, Matrix.mul_add, Matrix.trace_add]
  ring

theorem heatEulerGram_smul_left (r : ℝ) (A B : HeatEulerFiber) :
    heatEulerGram (r • A) B = r * heatEulerGram A B := by
  change 2 * (r * A.1) * B.1 - 2 * ((r • A.2.1)ᵀ * B.2.1).trace +
    ((r • A.2.2)ᵀ * B.2.2).trace = r *
      (2 * A.1 * B.1 - 2 * (A.2.1ᵀ * B.2.1).trace + (A.2.2ᵀ * B.2.2).trace)
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem heatEulerGram_smul_right (r : ℝ) (A B : HeatEulerFiber) :
    heatEulerGram A (r • B) = r * heatEulerGram A B := by
  change 2 * A.1 * (r * B.1) - 2 * (A.2.1ᵀ * (r • B.2.1)).trace +
    (A.2.2ᵀ * (r • B.2.2)).trace = r *
      (2 * A.1 * B.1 - 2 * (A.2.1ᵀ * B.2.1).trace + (A.2.2ᵀ * B.2.2).trace)
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  ring

theorem heatEulerGram_comm (A B : HeatEulerFiber) : heatEulerGram A B = heatEulerGram B A := by
  have ht₁ : (A.2.1ᵀ * B.2.1).trace = (B.2.1ᵀ * A.2.1).trace := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  have ht₂ : (A.2.2ᵀ * B.2.2).trace = (B.2.2ᵀ * A.2.2).trace := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [heatEulerGram, ht₁, ht₂]
  ring

theorem heatEulerGram_unit_left (A : HeatEulerFiber) :
    heatEulerGram heatEulerUnit A = heatEulerTrace A := by
  simp [heatEulerGram, heatEulerUnit, heatEulerTrace]

theorem heatEulerTrace_unit : heatEulerTrace heatEulerUnit = 0 := by
  norm_num [heatEulerTrace, heatEulerUnit]

theorem heatEulerGram_polynomial (U t : ℝ) (A B C : HeatEulerFiber) :
    heatEulerGram (U • heatEulerUnit + t • A + t ^ 2 • B + t ^ 3 • C)
      (U • heatEulerUnit + t • A + t ^ 2 • B + t ^ 3 • C) =
    2 * t * (U * heatEulerTrace A) + t ^ 2 *
      (2 * U * heatEulerTrace B + heatEulerGram A A +
        t * (2 * U * heatEulerTrace C + 2 * heatEulerGram A B) +
        t ^ 2 * (2 * heatEulerGram A C + heatEulerGram B B) +
        t ^ 3 * (2 * heatEulerGram B C) + t ^ 4 * heatEulerGram C C) := by
  simp only [heatEulerGram_add_left, heatEulerGram_add_right,
    heatEulerGram_smul_left, heatEulerGram_smul_right]
  rw [heatEulerGram_comm A heatEulerUnit, heatEulerGram_comm B heatEulerUnit,
    heatEulerGram_comm C heatEulerUnit, heatEulerGram_comm B A,
    heatEulerGram_comm C A, heatEulerGram_comm C B]
  simp only [heatEulerGram_unit_left, heatEulerTrace_unit]
  ring

theorem heatEulerGram_scalar_potential (a : ℝ) (V : HeatMat6)
    (hV : Vᵀ = V) (htr : V.trace = 24) :
    heatEulerGram (a, a • (1 : Mat4) - (3 : ℝ) • 1, a • (1 : HeatMat6) - V)
      (a, a • (1 : Mat4) - (3 : ℝ) • 1, a • (1 : HeatMat6) - V) =
        (V * V).trace - 72 := by
  simp only [heatEulerGram, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, hV, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub,
    Matrix.trace_smul, htr, smul_eq_mul]
  norm_num
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The surviving center coefficient of the actual Euler Gram expansion
is the Euler curvature polynomial with its exact Gaussian normalization. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalBundleExtension.eulerAmplitude (E : HeatNormalBundleExtension D)
    (m : ℕ) (x : FourSpace) : HeatEulerFiber :=
  (fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U m x,
    E.oneCompanion.amplitude m x, E.amplitude m x)

def HeatNormalBundleExtension.eulerSecondWeight (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  frameExponentialJacobian g o e x * χ x ^ 2 *
    (2 * E.base.U x * heatEulerTrace (E.eulerAmplitude 2 x) +
      heatEulerGram (E.eulerAmplitude 1 x) (E.eulerAmplitude 1 x))

omit [T3Space M] [CompactSpace M] in
theorem heatEuler_potential_density (hRic : RicciThree g) (e : FrameBundle g) :
    ((twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e) *
      twoFormPotentialMatrix (twoFormMetricCurvatureTensor g e)).trace - 72) /
      (32 * Real.pi ^ 2) = curvatureEulerDensity (twoFormMetricCurvatureTensor g e) := by
  have h := actual_hodgeEulerTracePolynomial hRic e
  have hl (i j k l : Fin 4) :
      twoFormMetricCurvatureTensor g e ![i,j,l,k] = -twoFormMetricCurvatureTensor g e ![i,j,k,l] := by
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  unfold hodgeEulerTracePolynomial at h
  simp only [connectionCurvature_euler_trace _ hl, Finset.sum_const_zero, zero_div, add_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact Euler polynomial and its vanishing lower-order term. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatEulerTrace_continuous : Continuous heatEulerTrace := by
  unfold heatEulerTrace Matrix.trace Matrix.diag
  fun_prop

theorem heatEulerGram_continuous :
    Continuous (fun z : HeatEulerFiber × HeatEulerFiber => heatEulerGram z.1 z.2) := by
  unfold heatEulerGram Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.eulerAmplitude_continuous
    (E : HeatNormalBundleExtension D) (m : ℕ) (hm : m ≤ 3) : Continuous (E.eulerAmplitude m) := by
  have hs : ContDiff ℝ 1 (fourHeatCoefficient E.base.a E.base.b (fun _ => 0) E.base.U m) :=
    fourHeatCoefficient_contDiff m 1 _ _ _ _
      (fun i j => (E.base.a_regular i j).of_le (by exact_mod_cast (show 1 + 3 * m ≤ 10 by omega)))
      (fun i => (E.base.b_regular i).of_le (by exact_mod_cast (show 1 + 3 * m ≤ 10 by omega)))
      contDiff_const (E.base.U_regular.of_le (by exact_mod_cast (show 1 + 3 * m ≤ 10 by omega)))
      (fun y => (E.base.U_pos y).ne')
  exact hs.continuous.prodMk
    ((continuous_pi (fun k => continuous_pi (fun l =>
      (E.oneCompanion.amplitude_regular m hm k l).continuous))).prodMk
      (continuous_pi (fun k => continuous_pi (fun l => (E.amplitude_regular m hm k l).continuous))))

def HeatNormalBundleExtension.eulerFirst (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  frameExponentialJacobian g o e x * χ x ^ 2 * E.base.U x * heatEulerTrace (E.eulerAmplitude 1 x)

def HeatNormalBundleExtension.eulerTail (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) : ℝ :=
  frameExponentialJacobian g o e x * χ x ^ 2 *
    (2 * E.base.U x * heatEulerTrace (E.eulerAmplitude 2 x) +
      heatEulerGram (E.eulerAmplitude 1 x) (E.eulerAmplitude 1 x) +
      t * (2 * E.base.U x * heatEulerTrace (E.eulerAmplitude 3 x) +
        2 * heatEulerGram (E.eulerAmplitude 1 x) (E.eulerAmplitude 2 x)) +
      t ^ 2 * (2 * heatEulerGram (E.eulerAmplitude 1 x) (E.eulerAmplitude 3 x) +
        heatEulerGram (E.eulerAmplitude 2 x) (E.eulerAmplitude 2 x)) +
      t ^ 3 * (2 * heatEulerGram (E.eulerAmplitude 2 x) (E.eulerAmplitude 3 x)) +
      t ^ 4 * heatEulerGram (E.eulerAmplitude 3 x) (E.eulerAmplitude 3 x))

def HeatNormalBundleExtension.eulerPolynomial (E : HeatNormalBundleExtension D)
    (t : ℝ) (x : FourSpace) : HeatEulerFiber :=
  E.eulerAmplitude 0 x + t • E.eulerAmplitude 1 x +
    t ^ 2 • E.eulerAmplitude 2 x + t ^ 3 • E.eulerAmplitude 3 x

theorem HeatNormalBundleExtension.eulerFirst_continuous (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) : Continuous (E.eulerFirst χ) :=
  (((frameExponentialJacobian_continuous g o e).mul (hχ.pow 2)).mul
    E.base.U_regular.continuous).mul
      (heatEulerTrace_continuous.comp (E.eulerAmplitude_continuous 1 (by norm_num)))

theorem HeatNormalBundleExtension.eulerFirst_compact (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hc : HasCompactSupport χ) : HasCompactSupport (E.eulerFirst χ) := by
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hn
  have hz := image_eq_zero_of_notMem_tsupport hn
  exact hx (by simp [HeatNormalBundleExtension.eulerFirst, hz])

theorem HeatNormalBundleExtension.eulerFirst_zero_near (E : HeatNormalBundleExtension D)
    (hRic : RicciThree g) (χ : FourSpace → ℝ) : E.eulerFirst χ =ᶠ[𝓝 0] fun _ => 0 := by
  filter_upwards [E.eulerFirstAmplitude_zero_near hRic] with x hx
  have ht : heatEulerTrace (E.eulerAmplitude 1 x) = 0 := hx
  simp only [eulerFirst, ht, mul_zero]

theorem HeatNormalBundleExtension.eulerTail_continuous (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : ℝ × FourSpace => E.eulerTail χ z.1 z.2) := by
  have hJ := (frameExponentialJacobian_continuous g o e).comp
    (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hU := E.base.U_regular.continuous.comp
    (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hS (m : ℕ) (hm : m ≤ 3) :=
    (heatEulerTrace_continuous.comp (E.eulerAmplitude_continuous m hm)).comp
      (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have hG (m n : ℕ) (hm : m ≤ 3) (hn : n ≤ 3) :=
    (heatEulerGram_continuous.comp ((E.eulerAmplitude_continuous m hm).prodMk
      (E.eulerAmplitude_continuous n hn))).comp
        (continuous_snd : Continuous (fun z : ℝ × FourSpace => z.2))
  have htwo : Continuous (fun _ : ℝ × FourSpace => (2 : ℝ)) := continuous_const
  have h0 := ((htwo.mul hU).mul (hS 2 (by norm_num))).add (hG 1 1 (by norm_num) (by norm_num))
  have h1 := ((htwo.mul hU).mul (hS 3 (by norm_num))).add
    (htwo.mul (hG 1 2 (by norm_num) (by norm_num)))
  have h2 := (htwo.mul (hG 1 3 (by norm_num) (by norm_num))).add (hG 2 2 (by norm_num) (by norm_num))
  unfold eulerTail
  exact (hJ.mul ((hχ.comp continuous_snd).pow 2)).mul
    ((((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul h2)).add
      ((continuous_fst.pow 3).mul (htwo.mul (hG 2 3 (by norm_num) (by norm_num))))).add
        ((continuous_fst.pow 4).mul (hG 3 3 (by norm_num) (by norm_num))))

theorem HeatNormalBundleExtension.eulerTail_bound (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, ‖E.eulerTail χ t x‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hc).exists_bound_of_continuousOn
    (E.eulerTail_continuous χ hχ).continuousOn
  refine ⟨max B 0, le_max_right _ _, fun t ht x => ?_⟩
  by_cases hx : x ∈ tsupport χ
  · exact (hB (t, x) ⟨ht, hx⟩).trans (le_max_left _ _)
  · have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [HeatNormalBundleExtension.eulerTail, hz, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_mul, norm_zero]
    exact le_max_right _ _

theorem HeatNormalBundleExtension.eulerTail_zero (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) : E.eulerTail χ 0 0 = E.eulerSecondWeight χ 0 := by
  simp only [eulerTail, eulerSecondWeight, zero_mul, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), zero_pow (by norm_num : 4 ≠ 0), add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common actual normal chart and cutoff for all three Euler heat degrees. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

structure HeatEulerChartData (D : HeatNormalFrameData g o c e) where
  base : HeatNormalExtension 10 g o e
  prototype : HeatNormalBundleExtension D
  normal : HeatNormalParametrixData D
  point_regular : ContDiffOn ℝ 4 D.point normal.chart.source
  inverse_regular : ContMDiffOn I4 I4 4 normal.chart.symm normal.chart.target

variable {D : HeatNormalFrameData g o c e}

def HeatEulerChartData.bundle (P : HeatEulerChartData D) : HeatNormalBundleExtension D :=
  { P.prototype with base := P.base }

def HeatEulerChartData.scalar (P : HeatEulerChartData D) : HeatScalarChartData D :=
  { P.normal with
    extension := P.base
    point_regular := P.point_regular
    inverse_regular := P.inverse_regular }

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed Gram integral of the actual normalized normal columns. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalPolynomialColumn_matrix (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) (x : FourSpace) :
    heatNormalPolynomialColumn E χ t l x =
      χ x • (WithLp.toLp 2 (fun k => heatNormalMatrixPolynomial E t x k l) : TwoFormFour) := by
  apply WithLp.ofLp_injective 2
  funext k
  exact congrArg (fun r : ℝ => χ x * r) (heatNormalMatrixPolynomial_component E t x k l).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The three genuine compact column polynomials are one Euler polynomial. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatEulerChartData.polynomial_scalar (P : HeatEulerChartData D) (t : ℝ) (x : FourSpace) :
    P.scalar.polynomial t x = P.normal.cutoff x * (P.bundle.eulerPolynomial t x).1 := by
  change P.normal.cutoff x * fourHeatPolynomial
    (fun m => fourHeatCoefficient P.base.a P.base.b (fun _ => 0) P.base.U m) t x = _
  simp only [HeatNormalBundleExtension.eulerPolynomial, HeatNormalBundleExtension.eulerAmplitude,
    Prod.fst_add, fourHeatPolynomial]
  rfl

theorem HeatEulerChartData.polynomial_one (P : HeatEulerChartData D)
    (t : ℝ) (l : Fin 4) (x : FourSpace) :
    heatNormalOnePolynomialColumn P.bundle.oneCompanion P.normal.cutoff t l x =
      P.normal.cutoff x • (WithLp.toLp 2
        (fun k => (P.bundle.eulerPolynomial t x).2.1 k l) : FourSpace) := by
  apply WithLp.ofLp_injective 2
  funext k
  change P.normal.cutoff x * fourHeatPolynomial
    (fun m y => P.bundle.oneCompanion.amplitude m y k l) t x = _
  simp only [HeatNormalBundleExtension.eulerPolynomial, HeatNormalBundleExtension.eulerAmplitude,
    Prod.snd_add, Prod.fst_add, Matrix.add_apply, fourHeatPolynomial]
  rfl

theorem HeatEulerChartData.polynomial_two (P : HeatEulerChartData D)
    (t : ℝ) (l : Fin 6) (x : FourSpace) :
    heatNormalPolynomialColumn P.bundle P.normal.cutoff t l x =
      P.normal.cutoff x • (WithLp.toLp 2
        (fun k => (P.bundle.eulerPolynomial t x).2.2 k l) : TwoFormFour) := by
  rw [heatNormalPolynomialColumn_matrix]
  rfl

theorem HeatEulerChartData.polynomial_euler (P : HeatEulerChartData D) (t : ℝ) (x : FourSpace) :
    2 * (P.scalar.polynomial t x) ^ 2 -
      2 * (∑ l : Fin 4, ‖heatNormalOnePolynomialColumn P.bundle.oneCompanion P.normal.cutoff t l x‖ ^ 2) +
      (∑ l : Fin 6, ‖heatNormalPolynomialColumn P.bundle P.normal.cutoff t l x‖ ^ 2) =
    P.normal.cutoff x ^ 2 * heatEulerGram (P.bundle.eulerPolynomial t x)
      (P.bundle.eulerPolynomial t x) := by
  rw [heatEulerGram_columns, P.polynomial_scalar]
  simp_rw [P.polynomial_one, P.polynomial_two, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [← Finset.mul_sum]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact integration of the common scalar and form column polynomials. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.eulerPolynomial_continuous
    (E : HeatNormalBundleExtension D) (t : ℝ) : Continuous (E.eulerPolynomial t) :=
  (((E.eulerAmplitude_continuous 0 (by norm_num)).add
    ((E.eulerAmplitude_continuous 1 (by norm_num)).const_smul t)).add
      ((E.eulerAmplitude_continuous 2 (by norm_num)).const_smul (t ^ 2))).add
        ((E.eulerAmplitude_continuous 3 (by norm_num)).const_smul (t ^ 3))

theorem HeatEulerChartData.scalar_polynomial_integrable (P : HeatEulerChartData D) (t : ℝ) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * (P.scalar.polynomial t x) ^ 2)) := by
  have h := heatEuler_cutoff_integrable (g := g) (o := o) (e := e) P.normal.cutoff
    (fun x => (P.bundle.eulerPolynomial t x).1 ^ 2) P.normal.cutoff_regular.continuous
    P.normal.cutoff_compact ((P.bundle.eulerPolynomial_continuous t).fst.pow 2) t
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [P.polynomial_scalar]
  ring

theorem HeatEulerChartData.one_polynomial_integrable (P : HeatEulerChartData D)
    (t : ℝ) (l : Fin 4) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalOnePolynomialColumn P.bundle.oneCompanion P.normal.cutoff t l x‖ ^ 2)) := by
  have he := (P.bundle.eulerPolynomial_continuous t).snd.fst
  have hcol : Continuous (fun x => (WithLp.toLp 2
      (fun k => (P.bundle.eulerPolynomial t x).2.1 k l) : FourSpace)) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      (continuous_apply l).comp ((continuous_apply k).comp he))
  have h := heatEuler_cutoff_integrable (g := g) (o := o) (e := e) P.normal.cutoff
    (fun x => ‖(WithLp.toLp 2 (fun k => (P.bundle.eulerPolynomial t x).2.1 k l) : FourSpace)‖ ^ 2)
    P.normal.cutoff_regular.continuous P.normal.cutoff_compact (hcol.norm.pow 2) t
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  rw [P.polynomial_one, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

theorem HeatEulerChartData.two_polynomial_integrable (P : HeatEulerChartData D)
    (t : ℝ) (l : Fin 6) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalPolynomialColumn P.bundle P.normal.cutoff t l x‖ ^ 2)) := by
  simpa only [real_inner_self_eq_norm_sq] using P.normal.polynomial_pair_integrable P.bundle t l l

theorem HeatEulerChartData.euler_integral (P : HeatEulerChartData D) (t : ℝ) :
    2 * (∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * (P.scalar.polynomial t x) ^ 2)) -
    2 * (∑ l : Fin 4, ∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalOnePolynomialColumn P.bundle.oneCompanion P.normal.cutoff t l x‖ ^ 2)) +
    (∑ l : Fin 6, ∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x *
        ‖heatNormalPolynomialColumn P.bundle P.normal.cutoff t l x‖ ^ 2)) =
    ∫ x, fourHeatGaussian t x ^ 2 *
      (frameExponentialJacobian g o e x * P.normal.cutoff x ^ 2 *
        heatEulerGram (P.bundle.eulerPolynomial t x) (P.bundle.eulerPolynomial t x)) := by
  let F₀ := fun x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x * (P.scalar.polynomial t x) ^ 2)
  let F₁ := fun l x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x *
      ‖heatNormalOnePolynomialColumn P.bundle.oneCompanion P.normal.cutoff t l x‖ ^ 2)
  let F₂ := fun l x => fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x *
      ‖heatNormalPolynomialColumn P.bundle P.normal.cutoff t l x‖ ^ 2)
  have h₀ : Integrable F₀ := P.scalar_polynomial_integrable t
  have h₁ (l : Fin 4) : Integrable (F₁ l) := P.one_polynomial_integrable t l
  have h₂ (l : Fin 6) : Integrable (F₂ l) := P.two_polynomial_integrable t l
  have hs₁ : Integrable (fun x => ∑ l, F₁ l x) := integrable_finsetSum _ (fun l _ => h₁ l)
  have hs₂ : Integrable (fun x => ∑ l, F₂ l x) := integrable_finsetSum _ (fun l _ => h₂ l)
  change 2 * (∫ x, F₀ x) - 2 * (∑ l, ∫ x, F₁ l x) + (∑ l, ∫ x, F₂ l x) = _
  rw [← integral_finsetSum _ (fun l _ => h₁ l), ← integral_finsetSum _ (fun l _ => h₂ l),
    ← integral_const_mul, ← integral_const_mul, ← integral_sub (h₀.const_mul 2) (hs₁.const_mul 2)]
  change (∫ x, ((fun y => 2 * F₀ y) - (fun y => 2 * ∑ l, F₁ l y)) x) +
    (∫ x, ∑ l, F₂ l x) = _
  rw [← integral_add ((h₀.const_mul 2).sub (hs₁.const_mul 2)) hs₂]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [Pi.sub_apply, F₀, F₁, F₂]
    rw [mul_assoc (frameExponentialJacobian g o e x) (P.normal.cutoff x ^ 2),
      ← P.polynomial_euler t x]
    simp only [mul_add, mul_sub, Finset.mul_sum, mul_left_comm]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


