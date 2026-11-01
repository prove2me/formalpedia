-- Prove2me | Definitions.Def_OAIQ091C028
-- name    : OAIQ091C028
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:52:14.656543+00:00
-- url     : https://prove2.me/theorems/d2ab7e3b-8459-4b50-ab09-9095a712e181
-- title:
--   Definitions bundle OAIQ091C028 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 257 declarations of OpenAI's Lean: 38 definitions and 219 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.HeatFamilyOneCoefficients.normalExtension`, `OAI.PositiveEinsteinFour.Geometry.HeatFamilySmoothCoefficients.normalExtension`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.normalizedResidual`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.normalizedResidualZero`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.residual`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.timeColumn`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.laplacianColumn`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.normalizedResidual`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.normalizedResidualZero`, `OAI.PositiveEinsteinFour.Geometry.HeatScalarChartData.residual`, `OAI.PositiveEinsteinFour.Geometry.TwoFormChartSobolev`, `OAI.PositiveEinsteinFour.Geometry.divergenceCokernelMean`, `OAI.PositiveEinsteinFour.Geometry.heatNormalGlobalTimeColumn`, `OAI.PositiveEinsteinFour.Geometry.localContinuousCutoff`, `OAI.PositiveEinsteinFour.Geometry.oneFormExactHeatTrace`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatSpectralTrace`, `OAI.PositiveEinsteinFour.Geometry.smoothH1Hodge`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicHodge`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicMinus`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPlus`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicSumEquiv`, `OAI.PositiveEinsteinFour.Geometry.smoothHarmonicSumLinear`, `OAI.PositiveEinsteinFour.Geometry.twoFormH1Hodge`, `OAI.PositiveEinsteinFour.Geometry.twoFormH1HodgeIsometry`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeat`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatChartL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatConvolution`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatLift`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatLiftSource`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatPowerSource`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatRate`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatSpectralTrace`, `OAI.PositiveEinsteinFour.Geometry.twoFormHeatWeight`, `OAI.PositiveEinsteinFour.Geometry.twoFormL2HodgeIsometry`, `OAI.PositiveEinsteinFour.Geometry.twoFormSpectralEquiv`, `OAI.PositiveEinsteinFour.Geometry.twoFormSpectralMultiplier`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory06.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C042`, `OAIQ091C024` and `OAIQ091C043` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C030`, `OAIQ091C031`, `OAIQ091C048`, `OAIQ091C049`, `OAIQ091C050` and `OAIQ091C053`; the proof of `OAI_PositiveEinsteinFour_Bianchi_rawCostCoefficient_pairing`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C042
import Definitions.Def_OAIQ091C024
import Definitions.Def_OAIQ091C043

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Extension of the actual Hodge involution to the L2 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormL2Hodge_involutive : Function.Involutive (twoFormL2Hodge (o := o)) := by
  have he : (fun u : TwoFormL2 o => twoFormL2Hodge (twoFormL2Hodge u)) = id := by
    apply smoothTwoFormToL2_dense.equalizer
      (twoFormL2Hodge.continuous.comp twoFormL2Hodge.continuous) continuous_id
    funext u
    change twoFormL2Hodge (twoFormL2Hodge (smoothTwoFormToL2 u)) = smoothTwoFormToL2 u
    rw [twoFormL2Hodge_smooth, twoFormL2Hodge_smooth]
    exact congrArg smoothTwoFormToL2 (smoothL2HodgeLinear_involutive u)
  exact congrFun he

theorem twoFormL2Hodge_norm (u : TwoFormL2 o) : ‖twoFormL2Hodge u‖ = ‖u‖ := by
  have he : (fun u : TwoFormL2 o => ‖twoFormL2Hodge u‖) = fun u => ‖u‖ := by
    apply smoothTwoFormToL2_dense.equalizer
      (continuous_norm.comp twoFormL2Hodge.continuous) continuous_norm
    funext v
    change ‖twoFormL2Hodge (smoothTwoFormToL2 v)‖ = ‖smoothTwoFormToL2 v‖
    rw [twoFormL2Hodge_smooth, smoothTwoFormToL2.norm_map,
      smoothTwoFormToL2.norm_map, smoothL2Hodge.norm_map]
  exact congrFun he u

def twoFormL2HodgeIsometry : TwoFormL2 o →ₗᵢ[ℝ] TwoFormL2 o where
  toLinearMap := twoFormL2Hodge.toLinearMap
  norm_map' := twoFormL2Hodge_norm

theorem twoFormL2Hodge_inner (u v : TwoFormL2 o) :
    inner ℝ (twoFormL2Hodge u) (twoFormL2Hodge v) = inner ℝ u v :=
  twoFormL2HodgeIsometry.inner_map_map u v

theorem twoFormL2Hodge_selfAdjoint (u v : TwoFormL2 o) :
    inner ℝ (twoFormL2Hodge u) v = inner ℝ u (twoFormL2Hodge v) := by
  have h := twoFormL2Hodge_inner u (twoFormL2Hodge v)
  rw [twoFormL2Hodge_involutive v] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Hodge star preserves covariant energy, hence the H1 norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.covariantPairing_hodge_self {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (x : M) :
    twoFormCovariantPairing o (fun y => twoFormHodge (u y)) (fun y => twoFormHodge (u y)) x =
      twoFormCovariantPairing o u u x := by
  obtain ⟨S, hS, U, hU, hxU, hUt, hp⟩ := twoForm_positive_chart o x
  let z := chartAt FourSpace x x
  let e := chartGramSection g x S hS ⟨z, hUt hxU⟩
  have hb : e.base = x := (chartAt FourSpace x).left_inv (mem_chart_source FourSpace x)
  rw [← hb, twoFormCovariantPairing_eq_frame, twoFormCovariantPairing_eq_frame]
  have hplain := hu.gramCovariantDerivative x S hS U hU hUt hp z hxU
  have hstar := hu.hodge.gramCovariantDerivative x S hS U hU hUt hp z hxU
  change (1 / 2 : ℝ) * frameTensorSquareNorm
    (twoFormFramedCovariantDerivative o (fun y => twoFormHodge (u y)) e) =
      (1 / 2 : ℝ) * frameTensorSquareNorm (twoFormFramedCovariantDerivative o u e)
  rw [hplain, hstar]
  have hr : twoFormLocalNablaRows (g := g) x S
      (twoFormChartValue o (fun y => twoFormHodge (u y)) x S hS) z =
      fun i => twoFormHodge (twoFormLocalNablaRows (g := g) x S (twoFormChartValue o u x S hS) z i) := by
    funext i
    exact hu.localNablaRows_hodge x S hS U hU hUt hp z hxU i
  rw [hr, twoFormDerivativeRows_hodge_norm]

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormCovariantEnergy_hodge (u : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy (smoothTwoFormHodge o u) (smoothTwoFormHodge o u) =
      smoothTwoFormCovariantEnergy u u := by
  apply integral_congr_ae
  filter_upwards [] with x
  exact u.property.covariantPairing_hodge_self x

def smoothH1Hodge : SmoothH1TwoForm o →ₗᵢ[ℝ] SmoothH1TwoForm o where
  toLinearMap := smoothTwoFormHodge o
  norm_map' u := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [smoothH1TwoForm_norm_sq, smoothH1TwoForm_norm_sq]
    exact congrArg₂ (· + ·) (smoothTwoFormL2Inner_hodge_self (u : smoothTwoForms o))
      (smoothTwoFormCovariantEnergy_hodge (u : smoothTwoForms o))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hodge involution on the actual H1 completion, compatible with its
L2 value map. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormH1Hodge : TwoFormH1 o →L[ℝ] TwoFormH1 o :=
  (smoothH1Hodge (o := o)).toContinuousLinearMap.completion

theorem twoFormH1Hodge_smooth (u : SmoothH1TwoForm o) :
    twoFormH1Hodge (smoothTwoFormToH1 u) = smoothTwoFormToH1 (smoothH1Hodge u) :=
  ContinuousLinearMap.completion_apply_coe _ u

theorem twoFormH1Hodge_norm (u : TwoFormH1 o) : ‖twoFormH1Hodge u‖ = ‖u‖ := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (continuous_norm.comp twoFormH1Hodge.continuous) continuous_norm) ?_
  intro v
  change ‖twoFormH1Hodge (smoothTwoFormToH1 v)‖ = ‖smoothTwoFormToH1 v‖
  rw [twoFormH1Hodge_smooth, smoothTwoFormToH1.norm_map, smoothTwoFormToH1.norm_map,
    smoothH1Hodge.norm_map]

theorem twoFormH1Hodge_involutive : Function.Involutive (twoFormH1Hodge (o := o)) := by
  intro u
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (twoFormH1Hodge.continuous.comp twoFormH1Hodge.continuous) continuous_id) ?_
  intro v
  change twoFormH1Hodge (twoFormH1Hodge (smoothTwoFormToH1 v)) = smoothTwoFormToH1 v
  rw [twoFormH1Hodge_smooth, twoFormH1Hodge_smooth]
  exact congrArg smoothTwoFormToH1 (smoothTwoFormHodge_involutive o v)

theorem twoFormH1ToL2_hodge (u : TwoFormH1 o) :
    twoFormH1ToL2 (twoFormH1Hodge u) = twoFormL2Hodge (twoFormH1ToL2 u) := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (twoFormH1ToL2.continuous.comp twoFormH1Hodge.continuous)
      (twoFormL2Hodge.continuous.comp twoFormH1ToL2.continuous)) ?_
  intro v
  change twoFormH1ToL2 (twoFormH1Hodge (smoothTwoFormToH1 v)) =
    twoFormL2Hodge (twoFormH1ToL2 (smoothTwoFormToH1 v))
  rw [twoFormH1Hodge_smooth, twoFormH1ToL2_smooth, twoFormH1ToL2_smooth, twoFormL2Hodge_smooth]
  rfl

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

theorem curvatureRow_hodge_pairing (R : CovariantCoordinates 4)
    (hl : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l])
    (hp : ∀ i j k l, R ![k,l,i,j] = R ![i,j,k,l]) (i j : Fin 4) :
    2 * inner ℝ (twoFormCurvatureRow R i j) (twoFormHodge (twoFormCurvatureRow R i j)) =
      ∑ k, ∑ l, R ![i,j,k,l] * hodgeFirstTensor R ![k,l,i,j] := by
  rw [← twoFormMatrix_pairing, twoFormMatrix_hodge, twoFormMatrix_curvatureRow R hl]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  change hodgeStarFour (fun p q => R ![i,j,p,q]) k l =
    hodgeStarFour (fun p q => R ![p,q,i,j]) k l
  apply congrArg (fun A : Mat4 => hodgeStarFour A k l)
  funext p q
  exact (hp i j p q).symm

theorem connectionCurvature_signature_trace (R : CovariantCoordinates 4)
    (hl : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l])
    (hp : ∀ i j k l, R ![k,l,i,j] = R ![i,j,k,l]) :
    (∑ i, ∑ j, (twoFormHodgeMatrix * twoFormConnectionCurvatureMatrix R i j *
      twoFormConnectionCurvatureMatrix R i j).trace) =
        -2 * frameTensorPairing R (hodgeFirstTensor R) := by
  have hi : 2 * (∑ i, ∑ j, inner ℝ (twoFormCurvatureRow R i j)
      (twoFormHodge (twoFormCurvatureRow R i j))) = frameTensorPairing R (hodgeFirstTensor R) := by
    simp only [Finset.mul_sum, curvatureRow_hodge_pairing R hl hp]
    rw [sum_pair_flip]
    rw [frameTensorPairing, sum_four_components_connection]
    repeat' (apply Finset.sum_congr rfl; intro _ _)
    congr 1
    exact hp _ _ _ _
  simp only [twoFormConnectionCurvatureMatrix, Matrix.mul_neg, Matrix.neg_mul,
    neg_neg, twoFormInfinitesimalMatrix_signed_square_trace, ← Finset.mul_sum]
  linarith only [hi]

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem actual_hodgeSignatureTracePolynomial (_hRic : RicciThree g) (e : FrameBundle g) :
    hodgeSignatureTracePolynomial (twoFormMetricCurvatureTensor g e) =
      curvatureSignatureDensity (twoFormMetricCurvatureTensor g e) := by
  let R := twoFormMetricCurvatureTensor g e
  have hf (i j k l : Fin 4) : R ![j,i,k,l] = -R ![i,j,k,l] :=
    twoFormMetricCurvatureTensor_skew g e i j k l
  have hl (i j k l : Fin 4) : R ![i,j,l,k] = -R ![i,j,k,l] := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_lastSkew e.frame i j k l
  have hp (i j k l : Fin 4) : R ![k,l,i,j] = R ![i,j,k,l] := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_pairSymmetric e.frame (frame_algebraic_lastSkew e.frame) i j k l
  have hb (i j k l : Fin 4) : R ![i,j,k,l] + R ![j,k,i,l] + R ![k,i,j,l] = 0 := by
    simp only [R, twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
    exact frame_algebraic_firstBianchi e.frame i j k l
  change hodgeSignatureTracePolynomial R = curvatureSignatureDensity R
  rw [hodgeSignatureTracePolynomial, twoFormPotentialMatrix_signed_square R hf hl hp hb,
    connectionCurvature_signature_trace R hl hp, curvatureSignatureDensity, curvaturePontryaginDensity]
  ring

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


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
theorem twoFormFromContinuousTensor_norm_le (F : C(FrameBundle g, TwoTensorEuclidean)) :
    ‖twoFormFromContinuousTensor (o := o) F‖ ≤ ‖F‖ := by
  apply (twoFormFromTensorL2_norm_le _).trans
  have hnorm : ‖(ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ :
      C(FrameBundle g, TwoTensorEuclidean) →L[ℝ] Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o))‖
      ≤ 1 := by
    simpa [measureUnivNNReal] using
      ContinuousMap.toLp_norm_le (𝕜 := ℝ) (E := TwoTensorEuclidean) (p := 2)
        (canonicalFrameMeasure g o)
  exact (ContinuousLinearMap.le_opNorm _ F).trans
    ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg F)).trans_eq (one_mul _))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The four derivatives of the actual inverse normal chart needed to
transport the local parametrix and its cutoff to the manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heat_normal_chart_four (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ (r : ℝ) (C : OpenPartialHomeomorph FourSpace M), 0 < r ∧
      C.source = ball 0 r ∧ EqOn C (frameExponential g o e) C.source ∧
      ContMDiffOn I4 I4 4 C.symm C.target := by
  obtain ⟨C, hzero, hC⟩ := frameExponential_localChart g o e
  let F := fun v : FourSpace => chartAt FourSpace e.base (frameExponential g o e v)
  have hFs : ContDiffAt ℝ ∞ F 0 := frameExponential_chart_smoothAt_zero g o e.base e
    (mem_chart_source FourSpace e.base)
  have hF4 : ∀ᶠ v in 𝓝 (0 : FourSpace), ContDiffAt ℝ 4 F v :=
    (hFs.of_le (show (4 : ℕ∞ω) ≤ ∞ by first | simp | exact_mod_cast le_top)).eventually (by norm_num)
  have hunit : IsUnit (fderiv ℝ F 0) := by
    have hd := frameExponential_chart_strictDerivative_zero g o e.base e
      (mem_chart_source FourSpace e.base)
    rw [hd.hasFDerivAt.fderiv]
    simpa only [chartForwardOperator_center, ContinuousLinearMap.id_comp] using frameMap_isUnit g e
  have hu : ∀ᶠ v in 𝓝 (0 : FourSpace), IsUnit (fderiv ℝ F v) := by
    have hnear := (hFs.of_le (show (1 : ℕ∞ω) ≤ ∞ by first | simp | exact_mod_cast le_top)).continuousAt_fderiv one_ne_zero
    have h := hnear.preimage_mem_nhds (ContinuousLinearEquiv.isOpen.mem_nhds
      ⟨ContinuousLinearEquiv.ofUnit hunit.unit, hunit.unit_spec⟩)
    filter_upwards [h] with v hv
    obtain ⟨E, hE⟩ := hv
    exact hE ▸ E.toUnit.isUnit
  have hc : ∀ᶠ v in 𝓝 (0 : FourSpace), frameExponential g o e v ∈
      (chartAt FourSpace e.base).source :=
    (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace e.base).open_source.mem_nhds (by
        rw [frameExponential_zero]
        exact mem_chart_source FourSpace e.base))
  have hg : ∀ᶠ v in 𝓝 (0 : FourSpace), v ∈ C.source ∧
      frameExponential g o e v ∈ (chartAt FourSpace e.base).source ∧
      ContDiffAt ℝ 4 F v ∧ IsUnit (fderiv ℝ F v) := by
    filter_upwards [C.open_source.mem_nhds hzero, hc, hF4, hu] with v hv hvc hfv huv
    exact ⟨hv, hvc, hfv, huv⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hg
  let D := C.restrOpen (ball 0 r) isOpen_ball
  have hsource : D.source = ball 0 r :=
    inter_eq_right.mpr (fun v hv => (hball hv).1)
  have hD : EqOn D (frameExponential g o e) D.source := fun _ hv => hC hv.1
  refine ⟨r, D, hr, hsource, hD, ?_⟩
  intro y hy
  let v := D.symm y
  have hv : v ∈ D.source := D.map_target hy
  have hvb := hball (hsource ▸ hv)
  have heq : frameExponential g o e v = y := (hD hv).symm.trans (D.right_inv hy)
  have h := heat_normal_inverse_four g o e e.base v D hv hD hvb.2.1 hvb.2.2.1 hvb.2.2.2
  rw [heq] at h
  exact h.contMDiffWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! A genuine normal chart supporting a
finite-regularity parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatNormalFrameChart {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    ∃ (r : ℝ) (C : OpenPartialHomeomorph FourSpace M), 0 < r ∧
      C.source = ball 0 r ∧ EqOn C (frameExponential g o e) C.source ∧
      ContMDiffOn I4 I4 4 C.symm C.target ∧
      C.target ⊆ (chartAt FourSpace c).source ∧
      ContDiffOn ℝ 4 D.point C.source ∧ C.source ⊆ ball 0 D.radius := by
  obtain ⟨r₀, C₀, hr₀, hC₀, hE, hI⟩ := exists_heat_normal_chart_four g o e
  have hc : ∀ᶠ x in 𝓝 (0 : FourSpace),
      frameExponential g o e x ∈ (chartAt FourSpace c).source :=
    (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds (by rwa [frameExponential_zero]))
  have hreg : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 4 D.point x :=
    (D.regular.of_le (show (4 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), x ∈ C₀.source ∧
      frameExponential g o e x ∈ (chartAt FourSpace c).source ∧
      ContDiffAt ℝ 4 D.point x ∧ x ∈ ball 0 D.radius := by
    filter_upwards [hC₀ ▸ ball_mem_nhds (0 : FourSpace) hr₀, hc, hreg,
      ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx hcx hpx hdx
    exact ⟨hx, hcx, hpx, hdx⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let C := C₀.restrOpen (ball 0 r) isOpen_ball
  have hs : C.source = ball 0 r := inter_eq_right.mpr (fun x hx => (hball hx).1)
  have hCE : EqOn C (frameExponential g o e) C.source := fun x hx => hE hx.1
  refine ⟨r, C, hr, hs, hCE, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact (hI.contMDiffAt (C₀.open_target.mem_nhds hy.1)).contMDiffWithinAt
  · intro y hy
    have hx := C.map_target hy
    have ht := (hball (hs ▸ hx)).2.1
    rw [← hCE hx, C.right_inv hy] at ht
    exact ht
  · intro x hx
    exact (hball (hs ▸ hx)).2.2.1.contDiffWithinAt
  · intro x hx
    exact (hball (hs ▸ hx)).2.2.2

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The bounded metric curvature potential commutes with the actual
Hodge involution on an Einstein four-manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothL2Curvature_hodge (hRic : RicciThree g) (u : SmoothL2TwoForm o) :
    smoothL2Curvature (smoothL2Hodge u) = smoothL2Hodge (smoothL2Curvature u) := by
  apply Subtype.ext
  funext x
  exact twoFormMetricCurvatureAction_hodge hRic ⟨x,o.frame x⟩ ((u : smoothTwoForms o).val x)

theorem twoFormL2Curvature_hodge (hRic : RicciThree g) (u : TwoFormL2 o) :
    twoFormL2Curvature (twoFormL2Hodge u) = twoFormL2Hodge (twoFormL2Curvature u) := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_eq (twoFormL2Curvature.continuous.comp twoFormL2Hodge.continuous)
      (twoFormL2Hodge.continuous.comp twoFormL2Curvature.continuous)) ?_
  intro v
  change twoFormL2Curvature (twoFormL2Hodge (smoothTwoFormToL2 v)) =
    twoFormL2Hodge (twoFormL2Curvature (smoothTwoFormToL2 v))
  rw [twoFormL2Hodge_smooth, twoFormL2Curvature_smooth, twoFormL2Curvature_smooth,
    twoFormL2Hodge_smooth, smoothL2Curvature_hodge hRic]

theorem twoFormWeitzenbockPotential_hodge (hRic : RicciThree g) (u : TwoFormL2 o) :
    twoFormWeitzenbockPotential (twoFormL2Hodge u) =
      twoFormL2Hodge (twoFormWeitzenbockPotential u) := by
  change (2 : ℝ) • twoFormL2Curvature (twoFormL2Hodge u) - (5 : ℝ) • twoFormL2Hodge u = _
  rw [twoFormL2Curvature_hodge hRic]
  change _ = twoFormL2Hodge ((2 : ℝ) • twoFormL2Curvature u - (5 : ℝ) • u)
  rw [map_sub, map_smul, map_smul]

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.heatSignedTraceENorm
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Extract a continuous representative on a fixed smaller ball from actual local
H3 regularity. The cutoff and its L2 realization are constructed here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff _root_.Topology

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

def localContinuousCutoff : S :=
  (localContinuousBump.hasCompactSupport.comp_left
    (show Complex.ofReal (0 : ℝ) = 0 by rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp localContinuousBump.contDiff)

theorem localContinuousCutoff_apply (x : V) : localContinuousCutoff x = (localContinuousBump x : ℂ) := rfl

theorem localContinuousCutoff_support :
    tsupport (localContinuousCutoff : V → ℂ) ⊆ closedBall 0 (1 / 2) := by
  have hs : Function.support (localContinuousCutoff : V → ℂ) =
      Function.support (localContinuousBump : V → ℝ) := by
    ext x
    simp only [Function.mem_support, localContinuousCutoff_apply, ne_eq, Complex.ofReal_eq_zero]
  rw [tsupport, hs]
  change tsupport (localContinuousBump : V → ℝ) ⊆ _
  rw [localContinuousBump.tsupport_eq]
  exact Subset.refl _

theorem localContinuousCutoff_one {x : V} (hx : x ∈ ball 0 (1 / 4)) :
    localContinuousCutoff x = 1 := by
  change (localContinuousBump x : ℂ) = 1
  rw [localContinuousBump.one_of_mem_closedBall (ball_subset_closedBall hx), Complex.ofReal_one]

theorem scalar_local_H3_continuous_real_representative (u : Lp ℝ 2 (volume : Measure V))
    (hreg : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2) →
      MemSobolev 3 2 (smulLeftCLM ℂ φ (scalarComplexL2 u : T))) :
    ∃ f : V → ℝ, Continuous f ∧
      (u : V → ℝ) =ᵐ[volume.restrict (ball 0 (1 / 4))] f := by
  let φ := localContinuousCutoff
  have hc : HasCompactSupport (φ : V → ℂ) :=
    (isCompact_closedBall (0 : V) (1 / 2)).of_isClosed_subset (isClosed_tsupport _) localContinuousCutoff_support
  let v := scalarL2Multiply (φ.toLp ∞ volume) (scalarComplexL2 u)
  have hv : (v : T) = smulLeftCLM ℂ φ (scalarComplexL2 u : T) := by
    dsimp [v]
    rw [SchwartzMap.toLp]
    exact scalarL2Multiply_distribution _ φ.hasTemperateGrowth (φ.memLp ∞ volume) _
  have hveq : v =ᵐ[volume] fun x => φ x * scalarComplexL2 u x := by
    change ((φ.toLp ∞ volume) • scalarComplexL2 u : Lp ℂ 2 volume) =ᵐ[volume] _
    filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (φ.toLp ∞ volume) (scalarComplexL2 u),
      φ.coeFn_toLp ∞ volume] with x hx hφ
    simpa only [smul_eq_mul, Pi.mul_apply, hφ] using hx
  obtain ⟨f, hf, he⟩ := scalar_L2_H3_continuous_real_representative v
    (by rw [hv]; exact hreg φ hc localContinuousCutoff_support)
  refine ⟨f, hf, ?_⟩
  apply (ae_restrict_iff' isOpen_ball.measurableSet).mpr
  filter_upwards [he, hveq, scalarComplexL2_coe u] with x hx hvx hux
  intro hxB
  rw [hvx, localContinuousCutoff_one hxB, one_mul, hux, Complex.ofReal_re] at hx
  exact hx

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

theorem heatNormalMetric_det_of_chart_unit (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (c : M) (v : FourSpace)
    (hc : frameExponential g o e v ∈ (chartAt FourSpace c).source)
    (hunit : IsUnit (fderiv ℝ (fun z => chartAt FourSpace c (frameExponential g o e z)) v)) :
    (heatNormalMetric g o e v).det ≠ 0 := by
  have hcomp := mfderiv_comp v
    ((mdifferentiable_chart (I := I4) c).mdifferentiableAt hc)
    ((frameExponential_contMDiff g o e).mdifferentiable one_ne_zero v)
  rw [mfderiv_eq_fderiv] at hcomp
  change fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z)) v =
    (show FourSpace →L[ℝ] FourSpace from
      mfderiv I4 I4 (chartAt FourSpace c) (frameExponential g o e v)).comp
        (show FourSpace →L[ℝ] FourSpace from mfderiv I4 I4 (frameExponential g o e) v) at hcomp
  have hF : Function.Injective
      (fderiv ℝ (fun z => chartAt FourSpace c (frameExponential g o e z)) v) := by
    have hL : (ContinuousLinearEquiv.ofUnit hunit.unit : FourSpace →L[ℝ] FourSpace) =
        fderiv ℝ (fun z => chartAt FourSpace c (frameExponential g o e z)) v := hunit.unit_spec
    rw [← hL]
    exact (ContinuousLinearEquiv.ofUnit hunit.unit).injective
  have hD : Function.Injective (mfderiv I4 I4 (frameExponential g o e) v) := by
    intro a b hab
    apply hF
    change (fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z)) v)
      (show FourSpace from a) =
      (fderiv ℝ (fun z : FourSpace => chartAt FourSpace c (frameExponential g o e z)) v)
        (show FourSpace from b)
    rw [hcomp]
    exact congrArg (mfderiv I4 I4 (chartAt FourSpace c) (frameExponential g o e v)) hab
  exact (heatNormalMetric_posDef g o e v hD).det_pos.ne'

theorem heatNormalMetric_eventually_nondegenerate (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) :
    ∀ᶠ v in 𝓝 (0 : FourSpace), (heatNormalMetric g o e v).det ≠ 0 := by
  let F := fun v : FourSpace => chartAt FourSpace e.base (frameExponential g o e v)
  have hF : ContDiffAt ℝ 1 F 0 := frameExponential_chart_contDiffAt_zero g o e.base e
    (mem_chart_source FourSpace e.base)
  have hu : IsUnit (fderiv ℝ F 0) := by
    have h := frameExponential_chart_strictDerivative_zero g o e.base e
      (mem_chart_source FourSpace e.base)
    rw [h.hasFDerivAt.fderiv]
    simpa only [chartForwardOperator_center, ContinuousLinearMap.id_comp] using frameMap_isUnit g e
  have hnear : ∀ᶠ v in 𝓝 (0 : FourSpace),
      fderiv ℝ F v ∈ range ((↑) : (FourSpace ≃L[ℝ] FourSpace) → FourSpace →L[ℝ] FourSpace) :=
    (hF.continuousAt_fderiv one_ne_zero).preimage_mem_nhds
      (ContinuousLinearEquiv.isOpen.mem_nhds
        ⟨ContinuousLinearEquiv.ofUnit hu.unit, hu.unit_spec⟩)
  have hc : ∀ᶠ v in 𝓝 (0 : FourSpace),
      frameExponential g o e v ∈ (chartAt FourSpace e.base).source := by
    apply (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
    rw [frameExponential_zero]
    exact (chartAt FourSpace e.base).open_source.mem_nhds (mem_chart_source FourSpace e.base)
  filter_upwards [hnear, hc] with v hv hvc
  obtain ⟨L, hL⟩ := hv
  apply heatNormalMetric_det_of_chart_unit g o e e.base v hvc
  exact hL ▸ L.toUnit.isUnit

end
end PositiveEinsteinFour.Geometry
end


section

/-! Fourth-power integrability transfers through compact chart reconstruction
and the closed coordinate-to-frame domination inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter Function
open scoped Manifold ContDiff ENNReal BigOperators

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

theorem scalarChartReconstruction_memLp_four (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (f : Lp ℝ 2 (volume : Measure FourSpace)) (hf : MemLp (f : FourSpace → ℝ) 4 volume) :
    MemLp (scalarChartReconstruction g c hK hKt f : M → ℝ) 4 (normalizedVolume g) := by
  obtain ⟨D, hD, hb⟩ := scalarChart_reverse_eLpNorm_bound g c hK hKt
  have hs : support (scalarChartReconstructionFun c K f) ⊆
      (chartAt FourSpace c).symm '' K := by
    intro x hx
    by_contra hn
    exact hx (indicator_of_notMem hn _)
  have he : (fun z => scalarChartReconstructionFun c K f ((chartAt FourSpace c).symm z)) =ᵐ[
      volume.restrict K] f := by
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    exact scalarChartReconstructionFun_chart c hKt f hz
  have hfin : MemLp (scalarChartReconstructionFun c K f) 4 (normalizedVolume g) := by
    refine ⟨(scalarChartReconstructionFun_stronglyMeasurable c hK hKt
      (Lp.stronglyMeasurable f)).aestronglyMeasurable, ?_⟩
    apply lt_of_le_of_lt (hb 4 _ hs)
    rw [eLpNorm_congr_ae he]
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by positivity) hD))
      ((eLpNorm_mono_measure f Measure.restrict_le_self).trans_lt hf.2)
  exact (memLp_congr_ae (scalarChartReconstruction_coe g c hK hKt f).symm).mp hfin

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimension-four product needed by the first higher nonlinear gain:
an H2 scalar multiplied by an H3 scalar remains H2. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

local instance instFactLeENNRealOfNat_solutions_16_re876e2_1 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
/-- No pointwise differentiability of either factor is assumed. -/
theorem scalar_real_H2_H3_product (u v : L2)
    (hu : MemSobolev 2 2 (scalarComplexL2 u : T))
    (hv : MemSobolev 3 2 (scalarComplexL2 v : T)) :
    ∃ w : L2, MemSobolev 2 2 (scalarComplexL2 w : T) ∧
      (w : V → ℝ) =ᵐ[volume] fun x => u x * v x := by
  obtain ⟨fs, F, F4, _, _, hf, hF, hF4, _, hFco, _⟩ :=
    scalar_real_integer_approximation 2 u hu
  obtain ⟨gs, G, G4, Gtop, _, hg, hG, hG4, hGt, hGco, hGtco⟩ :=
    scalar_real_integer_approximation 3 v hv
  let w : L2 := scalarL4Product (F4 []) (G4 [])
  let Dw : Fin 4 → L2 := fun i =>
    scalarL4Product (F4 [i]) (G4 []) + scalarL4Product (F4 []) (G4 [i])
  let DDw : Fin 4 → Fin 4 → L2 := fun i j =>
    scalarLinfL2Product (Gtop []) (F [i,j]) +
    scalarL4Product (F4 [j]) (G4 [i]) +
    scalarL4Product (F4 [i]) (G4 [j]) +
    scalarL4Product (F4 []) (G4 [i,j])
  have hfs4 := hF4 [] (by simp)
  have hgs4 := hG4 [] (by simp)
  refine ⟨w, ?_, ?_⟩
  · apply scalar_real_H2_of_strong_jets (fun k => scalarRealSchwartzProduct (fs k) (gs k)) w Dw DDw
    · simp only [scalarRealSchwartzProduct_L2_four]
      exact scalarL4Product_tendsto hfs4 hgs4
    · intro i
      simp only [scalarRealSchwartzProduct_first_L2]
      exact (scalarL4Product_tendsto (hF4 [i] (by simp)) hgs4).add
        (scalarL4Product_tendsto hfs4 (hG4 [i] (by simp)))
    · intro i j
      simp only [scalarRealSchwartzProduct_second_L2]
      have h₀ := scalarLinfL2Product_tendsto (hGt [] (by simp)) (hF [i,j] (by simp))
      have h₁ := scalarL4Product_tendsto (hF4 [j] (by simp)) (hG4 [i] (by simp))
      have h₂ := scalarL4Product_tendsto (hF4 [i] (by simp)) (hG4 [j] (by simp))
      have h₃ := scalarL4Product_tendsto hfs4 (hG4 [i,j] (by simp))
      exact ((h₀.add h₁).add h₂).add h₃
  · have hFu : F [] = u := tendsto_nhds_unique (hF [] (by simp)) hf
    have hGv : G [] = v := tendsto_nhds_unique (hG [] (by simp)) hg
    filter_upwards [scalarL4Product_coe (F4 []) (G4 []), hFco [] (by simp), hGco [] (by simp)]
      with x hw hfx hgx
    change scalarL4Product (F4 []) (G4 []) x = _
    rw [hw, ← hfx, ← hgx, hFu, hGv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Real parts and real representatives preserve the finite integer Sobolev
orders used in the localized Euler bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology

noncomputable section

local notation "V" => FourSpace
local notation "C2" => Lp ℂ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

theorem scalar_realPart_memSobolev_integer (n : ℕ) (u : C2)
    (hu : MemSobolev (n : ℝ) 2 (u : T)) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (Complex.reCLM.compLp u) : T) := by
  obtain ⟨v, fs, _, _, hf, hG, _, _⟩ := scalar_integer_smooth_approximation n u hu
  let R := Complex.reCLM.compLpL 2 (volume : Measure V)
  let G := fun is : List (Fin 4) => if h : is.length ≤ n then R (scalarBesselJetL2 n is h v) else 0
  apply scalar_real_integer_jets_closed n (fun k => (fs k).postcompCLM Complex.reCLM) (R u) G
  · simp only [scalarSchwartz_re_toLp]
    exact R.continuous.continuousAt.tendsto.comp hf
  · intro is hs
    simp only [scalarRealSchwartzJet_re, scalarSchwartz_re_toLp, G, dite_eq_left hs]
    exact R.continuous.continuousAt.tendsto.comp (hG is hs)

theorem scalar_real_integer_realization (n : ℕ) (u : C2)
    (hu : MemSobolev (n : ℝ) 2 (u : T)) (b : V → ℝ)
    (hb : (u : V → ℂ) =ᵐ[volume] fun x => (b x : ℂ)) :
    ∃ v : Lp ℝ 2 (volume : Measure V), MemSobolev (n : ℝ) 2 (scalarComplexL2 v : T) ∧
      (v : V → ℝ) =ᵐ[volume] b := by
  refine ⟨Complex.reCLM.compLp u, scalar_realPart_memSobolev_integer n u hu, ?_⟩
  filter_upwards [Complex.reCLM.coeFn_compLp u, hb] with x hr hx
  rw [hr, hx]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first distributional product rule from actual H2 approximations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal _root_.Topology LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

local instance instFactLeENNRealOfNat_solutions_17_re876e2_1 : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
/-- The product of H2 factors has an L2 weak derivative with the actual
Leibniz formula. The result identifies the derivative of any L2 realization
of the pointwise product. -/
theorem scalar_real_weak_product (u v w du dv : L2)
    (hu : MemSobolev 2 2 (scalarComplexL2 u : T))
    (hv : MemSobolev 2 2 (scalarComplexL2 v : T))
    (hw : (w : V → ℝ) =ᵐ[volume] fun x => u x * v x)
    (i : Fin 4)
    (hdu : scalarCoordinateDerivative i (scalarComplexL2 u : T) = (scalarComplexL2 du : T))
    (hdv : scalarCoordinateDerivative i (scalarComplexL2 v : T) = (scalarComplexL2 dv : T)) :
    ∃ z : L2, scalarCoordinateDerivative i (scalarComplexL2 w : T) = (scalarComplexL2 z : T) ∧
      (z : V → ℝ) =ᵐ[volume] fun x => du x * v x + u x * dv x := by
  obtain ⟨fs, F, F4, _, _, hf, hF, hF4, _, hFco, _⟩ := scalar_real_integer_approximation 2 u hu
  obtain ⟨gs, G, G4, _, _, hg, hG, hG4, _, hGco, _⟩ := scalar_real_integer_approximation 2 v hv
  have hFu : F [] = u := tendsto_nhds_unique (hF [] (by simp)) hf
  have hGv : G [] = v := tendsto_nhds_unique (hG [] (by simp)) hg
  have hFdu : F [i] = du := scalar_real_L2_distribution_injective
    ((scalar_real_jet_limit [i] fs u (F [i]) hf (hF [i] (by simp))).symm.trans hdu)
  have hGdv : G [i] = dv := scalar_real_L2_distribution_injective
    ((scalar_real_jet_limit [i] gs v (G [i]) hg (hG [i] (by simp))).symm.trans hdv)
  let w₀ : L2 := scalarL4Product (F4 []) (G4 [])
  have hww : w₀ = w := by
    apply Lp.ext
    filter_upwards [scalarL4Product_coe (F4 []) (G4 []), hFco [] (by simp), hGco [] (by simp), hw]
      with x hp hfu hgv hwx
    change scalarL4Product (F4 []) (G4 []) x = _
    rw [hp, ← hfu, ← hgv, hFu, hGv, hwx]
  let z : L2 := scalarL4Product (F4 [i]) (G4 []) + scalarL4Product (F4 []) (G4 [i])
  refine ⟨z, ?_, ?_⟩
  · have hvalue : Tendsto (fun k => (scalarRealSchwartzProduct (fs k) (gs k)).toLp 2 volume)
        atTop (𝓝 w) := by
      simp only [scalarRealSchwartzProduct_L2_four]
      rw [← hww]
      exact scalarL4Product_tendsto (hF4 [] (by simp)) (hG4 [] (by simp))
    have hderiv : Tendsto (fun k => (scalarRealSchwartzJet [i]
        (scalarRealSchwartzProduct (fs k) (gs k))).toLp 2 volume) atTop (𝓝 z) := by
      change Tendsto (fun k => (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i}
        (scalarRealSchwartzProduct (fs k) (gs k))).toLp 2 volume) atTop (𝓝 z)
      simp only [scalarRealSchwartzProduct_first_L2]
      exact (scalarL4Product_tendsto (hF4 [i] (by simp)) (hG4 [] (by simp))).add
        (scalarL4Product_tendsto (hF4 [] (by simp)) (hG4 [i] (by simp)))
    exact scalar_real_jet_limit [i] _ w z hvalue hderiv
  · filter_upwards [Lp.coeFn_add (scalarL4Product (F4 [i]) (G4 []))
        (scalarL4Product (F4 []) (G4 [i])),
      scalarL4Product_coe (F4 [i]) (G4 []), scalarL4Product_coe (F4 []) (G4 [i]),
      hFco [i] (by simp), hGco [] (by simp), hFco [] (by simp), hGco [i] (by simp)]
      with x hsum hp hq hdu' hv' hu' hdv'
    change (scalarL4Product (F4 [i]) (G4 []) + scalarL4Product (F4 []) (G4 [i])) x = _
    rw [hsum, Pi.add_apply, hp, hq, ← hdu', ← hv', ← hu', ← hdv', hFdu, hGv, hFu, hGdv]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transport of the actual normal metric and its inverse by the base
Jacobian of the constructed frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.inverseMetric_transport_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    ∀ᶠ x in 𝓝 (0 : FourSpace),
      jacobianMatrix (fun y => (D.point y).1) x * (heatNormalMetric g o e x)⁻¹ *
        (jacobianMatrix (fun y => (D.point y).1) x)ᵀ = (metricInChart g c (D.point x).1)⁻¹ := by
  have hs : ∀ᶠ x in 𝓝 (0 : FourSpace), frameExponential g o e x ∈
      (chartAt FourSpace c).source :=
    (frameExponential_continuous g o e).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds (by simpa only [frameExponential_zero] using he))
  filter_upwards [hs, ball_mem_nhds (0 : FourSpace) D.radius_pos,
    heatNormalMetric_eventually_nondegenerate g o e] with x hs hx hg
  exact D.inverseMetric_transport x hx hs hg

end
end PositiveEinsteinFour.Geometry
end


section

/-! The H3 algebra in dimension four, using the actual H2-by-H3 product
and the first distributional Leibniz identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

/-- Two H3 functions have an actual H3 pointwise product. -/
theorem scalar_real_H3_product (u v : L2)
    (hu : MemSobolev 3 2 (scalarComplexL2 u : T))
    (hv : MemSobolev 3 2 (scalarComplexL2 v : T)) :
    ∃ w : L2, MemSobolev 3 2 (scalarComplexL2 w : T) ∧
      (w : V → ℝ) =ᵐ[volume] fun x => u x * v x := by
  obtain ⟨w, hw, hwe⟩ := scalar_real_H2_H3_product u v (hu.mono (by norm_num)) hv
  refine ⟨w, ?_, hwe⟩
  have hh := scalar_memSobolev_succ_iff 2 (scalarComplexL2 w : T)
  norm_num only [show (2 : ℝ) + 1 = 3 by norm_num] at hh
  apply hh.mpr
  refine ⟨hw, fun i => ?_⟩
  obtain ⟨du, hdu, hdu2⟩ := scalar_real_derivative_sobolev 2 u (by norm_num; exact hu) i
  obtain ⟨dv, hdv, hdv2⟩ := scalar_real_derivative_sobolev 2 v (by norm_num; exact hv) i
  obtain ⟨a, ha, hae⟩ := scalar_real_H2_H3_product du v hdu2 hv
  obtain ⟨b, hb, hbe⟩ := scalar_real_H2_H3_product dv u hdv2 hu
  obtain ⟨z, hz, hze⟩ := scalar_real_weak_product u v w du dv
    (hu.mono (by norm_num)) (hv.mono (by norm_num)) hwe i hdu hdv
  have he : z = a + b := by
    apply Lp.ext
    filter_upwards [hze, hae, hbe, Lp.coeFn_add a b] with x hz ha hb hab
    rw [hz, hab, Pi.add_apply, ha, hb]
    ring
  rw [hz, he]
  exact scalar_real_sobolev_add 2 a b ha hb

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized leading scalar amplitude solves its transport
equation on a normal-coordinate ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalLeadingAmplitude_transport_neighborhood (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r,
      fourHeatRadialTransport (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalLeadingAmplitude g o e) x = 0 := by
  let a := fun y => (heatNormalMetric g o e y)⁻¹
  let J := frameExponentialJacobian g o e
  let u := heatNormalLeadingAmplitude g o e
  have ha : ∀ᶠ x in 𝓝 (0 : FourSpace),
      ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have hn := ((heatNormalInverse_smoothAt_zero g o e i j).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    filter_upwards [hn] with x hx
    exact hx.differentiableAt one_ne_zero
  have hJ : ∀ᶠ x in 𝓝 (0 : FourSpace), DifferentiableAt ℝ J x := by
    have hn := ((frameExponentialJacobian_smoothAt_zero g o e).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    filter_upwards [hn] with x hx
    exact hx.differentiableAt one_ne_zero
  have hu : ∀ᶠ x in 𝓝 (0 : FourSpace), DifferentiableAt ℝ u x := by
    have hn := ((heatNormalLeadingAmplitude_smoothAt_zero g o e).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    filter_upwards [hn] with x hx
    exact hx.differentiableAt one_ne_zero
  have hnear : ∀ᶠ x in 𝓝 (0 : FourSpace),
      (∀ i j, DifferentiableAt ℝ (fun y => a y i j) x) ∧
      DifferentiableAt ℝ J x ∧ DifferentiableAt ℝ u x ∧
      (heatNormalMetric g o e x).det ≠ 0 ∧ 0 < J x := by
    filter_upwards [ha, hJ, hu, heatNormalMetric_eventually_nondegenerate g o e,
      frameExponentialJacobian_eventually_pos g o e] with x ha hJ hu hd hp
    exact ⟨ha, hJ, hu, hd, hp⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨r, hr, ?_⟩
  intro x hx
  have hrad : ∀ᶠ y in 𝓝 x, ∀ i, ∑ j : Fin 4, a y i j * y j = y i := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    intro i
    exact congrFun (heatNormalMetric_inverse_radial g o hRic e he y (hball hy).2.2.2.1) i
  have hcol : ∀ j, ∑ i : Fin 4, a x i j * x i = x j := by
    intro j
    have hs (i : Fin 4) : a x i j = a x j i :=
      congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    simp_rw [hs]
    exact hrad.self_of_nhds j
  have hnorm : ∀ᶠ y in 𝓝 x, u y ^ 2 * J y = 1 := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact heatNormalLeadingAmplitude_normalization g o e y (hball hy).2.2.2.2
  exact fourHeatDensity_leading_transport a J u x (hball hx).1
    (hball hx).2.1 (hball hx).2.2.1 hrad hcol hnorm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integer Sobolev products at the orders used after the first nonlinear
gain. The induction uses actual weak derivatives, starting with H3. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

theorem scalar_real_integer_product (n : ℕ) (hn : 3 ≤ n) :
    ∀ u v : L2, MemSobolev (n : ℝ) 2 (scalarComplexL2 u : T) →
      MemSobolev (n : ℝ) 2 (scalarComplexL2 v : T) →
      ∃ w : L2, MemSobolev (n : ℝ) 2 (scalarComplexL2 w : T) ∧
        (w : V → ℝ) =ᵐ[volume] fun x => u x * v x := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro u v hu hv
    exact scalar_real_H3_product u v hu hv
  | succ n hn ih =>
    intro u v hu hv
    have hu' : MemSobolev (n : ℝ) 2 (scalarComplexL2 u : T) :=
      hu.mono (by exact_mod_cast Nat.le_succ n)
    have hv' : MemSobolev (n : ℝ) 2 (scalarComplexL2 v : T) :=
      hv.mono (by exact_mod_cast Nat.le_succ n)
    obtain ⟨w, hw, hwe⟩ := ih u v hu' hv'
    refine ⟨w, ?_, hwe⟩
    have hreg : MemSobolev ((n : ℝ) + 1) 2 (scalarComplexL2 w : T) := by
      apply (scalar_memSobolev_succ_iff (n : ℝ) _).mpr
      refine ⟨hw, fun i => ?_⟩
      obtain ⟨du, hdu, hduN⟩ := scalar_real_derivative_sobolev n u
        (by simpa only [Nat.cast_add, Nat.cast_one] using hu) i
      obtain ⟨dv, hdv, hdvN⟩ := scalar_real_derivative_sobolev n v
        (by simpa only [Nat.cast_add, Nat.cast_one] using hv) i
      obtain ⟨a, ha, hae⟩ := ih du v hduN hv'
      obtain ⟨b, hb, hbe⟩ := ih u dv hu' hdvN
      have hu2 : MemSobolev 2 2 (scalarComplexL2 u : T) :=
        hu'.mono (by exact_mod_cast (show 2 ≤ n by omega))
      have hv2 : MemSobolev 2 2 (scalarComplexL2 v : T) :=
        hv'.mono (by exact_mod_cast (show 2 ≤ n by omega))
      obtain ⟨z, hz, hze⟩ := scalar_real_weak_product u v w du dv hu2 hv2 hwe i hdu hdv
      have he : z = a + b := by
        apply Lp.ext
        filter_upwards [hze, hae, hbe, Lp.coeFn_add a b] with x hz ha hb hab
        rw [hz, hab, Pi.add_apply, ha, hb]
      rw [hz, he]
      exact scalar_real_sobolev_add (n : ℝ) a b ha hb
    simpa only [Nat.cast_add, Nat.cast_one] using hreg

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

theorem heatFamilyDrift_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 2 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hdet : 0 < (heatFamilyMetric g c P z).det) (j : Fin 4) :
    ContDiffAt ℝ n (fun y => heatFamilyDrift g c P y j) z := by
  have hP1 : ContDiffAt ℝ (n + 1 + 1 : ℕ) P z := by simpa only [Nat.add_assoc] using hP
  have hA (i j : Fin 4) := heatFamilyInverse_contDiffAt (n + 1) g c P z hP1 hz hdet.ne' i j
  have hJ := heatFamilyDensity_contDiffAt (n + 1) g c P z hP1 hz hdet.ne'
  have hle : (n : ℕ∞ω) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
  have hJn : heatFamilyDensity g c P z ≠ 0 := (Real.sqrt_pos.mpr hdet).ne'
  apply ((ContDiffAt.sum (fun i _ =>
    heatFamilyScalarPartial_contDiffAt n _ z (hA i j) i)).add ?_).neg
  exact ((hJ.of_le hle).inv hJn).mul (ContDiffAt.sum (fun i _ =>
    ((hA i j).of_le hle).mul (heatFamilyScalarPartial_contDiffAt n _ z hJ i)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The drift used by the actual normal parametrix has the geometric
coordinate transformation law on a proved neighborhood of its center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.drift_transport_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ r : Fin 4,
      (∑ k, jacobianMatrix (fun y => (D.point y).1) x r k * heatNormalDrift g o e x k) -
        (∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
          partialDeriv (fun y => jacobianMatrix (fun z => (D.point z).1) y r j) i x) =
        ∑ p, ∑ q, (metricInChart g c (D.point x).1)⁻¹ p q *
          christoffel g c (D.point x).1 r p q := by
  let F := fun y => (D.point y).1
  have hF : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 F x :=
    (D.regular.fst.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hG := D.metric_pullback_near he
  filter_upwards [hF, hG.eventuallyEq_nhds, hG, frameExponentialJacobian_eventually_pos g o e,
    ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hFx hGx hG0 hρx hx
  intro r
  have hρ : 0 < (heatNormalMetric g o e x).det := Real.sqrt_pos.mp hρx
  have hd (k : Fin 4) : heatNormalDrift g o e x k =
      fourHeatDensityDrift (fun y => (heatPullbackMetric g c F y)⁻¹)
        (fun y => Real.sqrt (heatPullbackMetric g c F y).det) x k := by
    apply fourHeatDensityDrift_congr
    · exact hGx.mono fun y hy => congrArg Inv.inv hy
    · exact hGx.mono fun y hy => congrArg (fun G : Mat4 => Real.sqrt G.det) hy
  simp_rw [hd, hG0]
  exact heatPullback_drift_transport g c F x hFx (D.in_chart x hx)
    (by simpa only [hG0] using hρ) r

end
end PositiveEinsteinFour.Geometry
end


section

/-! Products with one extra Sobolev derivative, including the H2 endpoint,
for the localized positive-power bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)

theorem scalar_real_integer_product_extra (n : ℕ) (hn : 2 ≤ n) (u v : L2)
    (hu : MemSobolev (n : ℝ) 2 (scalarComplexL2 u : T))
    (hv : MemSobolev ((n : ℝ) + 1) 2 (scalarComplexL2 v : T)) :
    ∃ w : L2, MemSobolev (n : ℝ) 2 (scalarComplexL2 w : T) ∧
      (w : V → ℝ) =ᵐ[volume] fun x => u x * v x := by
  by_cases h : n = 2
  · subst n
    exact scalar_real_H2_H3_product u v hu (by norm_num at hv; exact hv)
  · exact scalar_real_integer_product n (by omega) u v hu (hv.mono (by linarith))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Recovery of the full actual Sobolev jet from its scalar Lp representative,
and the weighted pairing on smooth scalar functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarSmoothRep_frameCompact
local instance scalarSmoothRep_probability_re876e2_1 (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)
theorem smoothScalarToWeightedH1_inner (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (a b : SmoothScalar (M := M)) :
    inner ℝ (smoothScalarToWeightedH1 d a) (smoothScalarToWeightedH1 d b) =
      (∫ x, a.val x * b.val x ∂normalizedVolume g) + smoothScalarDirichlet d a b / 2 := by
  have hvalue : inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) a)
      (smoothScalarValueL2 g (canonicalFrameMeasure g o) b) =
        ∫ x, a.val x * b.val x ∂normalizedVolume g := by
    rw [← scalarBasePullback_smooth g o a, ← scalarBasePullback_smooth g o b,
      (scalarBasePullback g o).inner_map_map, smoothScalarBaseL2_inner]
  change inner ℝ (scalarWeightedH1Equiv d (smoothScalarToH1 d a))
    (scalarWeightedH1Equiv d (smoothScalarToH1 d b)) = _
  rw [scalarWeightedH1_inner]
  simp only [scalarH1Value_smooth, scalarH1Gradient_smooth, hvalue]
  change (∫ x, a.val x * b.val x ∂normalizedVolume g) +
      (1 / 2 : ℝ) * smoothScalarDirichlet d a b = _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity of the actual differential expression used in the
heat transport recursion. Each application loses two derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeatRadialTransport_germ (a : Mat4) (b : Fin 4 → ℝ)
    {u v : FourSpace → ℝ} {x : FourSpace} (h : u =ᶠ[nhds x] v) :
    fourHeatRadialTransport a b u x = fourHeatRadialTransport a b v x := by
  unfold fourHeatRadialTransport
  simp only [fourHeat_partial_germ h, h.self_of_nhds]

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

theorem heatFamilyZero_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 2 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hframe : (P z).2.det ≠ 0) (hmetric : 0 < (heatFamilyMetric g c P z).det)
    (k l : Fin 6) :
    ContDiffAt ℝ n (fun y => heatFamilyZero g c P y k l) z := by
  have hle : (n : ℕ∞ω) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
  have hP1 : ContDiffAt ℝ (n + 1 + 1 : ℕ) P z := by simpa only [Nat.add_assoc] using hP
  have hA (i : Fin 4) (k l : Fin 6) : ContDiffAt ℝ (n + 1 : ℕ)
      (fun y => heatFamilyTwoFormConnection g c P i y k l) z :=
    heatFamilyTwoFormConnection_contDiffAt (n + 1) g c P z hP1 hz hframe i k l
  have hA0 (i : Fin 4) (k l : Fin 6) := (hA i k l).of_le hle
  have hD (i j : Fin 4) (k l : Fin 6) :=
    heatFamilyScalarPartial_contDiffAt n _ z (hA i k l) j
  have hV := heatFamilyPotential_contDiffAt n g c P z
    (hP.of_le (by exact_mod_cast (show n ≤ n + 2 by omega))) hz k l
  have hInv (i j : Fin 4) := heatFamilyInverse_contDiffAt n g c P z
    (hP.of_le (by exact_mod_cast (show n + 1 ≤ n + 2 by omega))) hz hmetric.ne' i j
  change ContDiffAt ℝ n (fun y => heatFamilyPotential g c P y k l +
    (∑ i : Fin 4, heatFamilyDrift g c P y i * heatFamilyTwoFormConnection g c P i y k l) -
    ∑ i : Fin 4, ∑ j : Fin 4, (heatFamilyMetric g c P y)⁻¹ i j *
      (heatFamilyScalarPartial (fun w => heatFamilyTwoFormConnection g c P i w k l) j y +
        ∑ q : Fin 6, heatFamilyTwoFormConnection g c P j y k q *
          heatFamilyTwoFormConnection g c P i y q l)) z
  apply (hV.add (ContDiffAt.sum (fun i _ =>
    (heatFamilyDrift_contDiffAt n g c P z hP hz hmetric i).mul (hA0 i k l)))).sub
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (hInv i j).mul ((hD i j k l).add
    (ContDiffAt.sum (fun q _ => (hA0 j k q).mul (hA0 i q l))))

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

theorem heatFamilyOneZero_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ (n + 2 : ℕ) P z)
    (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hframe : (P z).2.det ≠ 0) (hmetric : 0 < (heatFamilyMetric g c P z).det)
    (k l : Fin 4) :
    ContDiffAt ℝ n (fun y => heatFamilyOneZero g c P y k l) z := by
  have hle : (n : ℕ∞ω) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_succ n
  have hP1 : ContDiffAt ℝ (n + 1 + 1 : ℕ) P z := by simpa only [Nat.add_assoc] using hP
  have hA (i : Fin 4) (k l : Fin 4) : ContDiffAt ℝ (n + 1 : ℕ)
      (fun y => heatFamilyConnection g c P i y k l) z :=
    heatFamilyConnection_contDiffAt (n + 1) g c P z hP1 hz hframe i k l
  have hA0 (i : Fin 4) (k l : Fin 4) := (hA i k l).of_le hle
  have hD (i j : Fin 4) (k l : Fin 4) :=
    heatFamilyScalarPartial_contDiffAt n _ z (hA i k l) j
  have hV : ContDiffAt ℝ n (fun _ : HeatRadialFrameSpace => ((3 : ℝ) • (1 : Mat4)) k l) z := contDiffAt_const
  have hInv (i j : Fin 4) := heatFamilyInverse_contDiffAt n g c P z
    (hP.of_le (by exact_mod_cast (show n + 1 ≤ n + 2 by omega))) hz hmetric.ne' i j
  change ContDiffAt ℝ n (fun y => ((3 : ℝ) • (1 : Mat4)) k l +
    (∑ i : Fin 4, heatFamilyDrift g c P y i * heatFamilyConnection g c P i y k l) -
    ∑ i : Fin 4, ∑ j : Fin 4, (heatFamilyMetric g c P y)⁻¹ i j *
      (heatFamilyScalarPartial (fun w => heatFamilyConnection g c P i w k l) j y +
        ∑ q : Fin 4, heatFamilyConnection g c P j y k q *
          heatFamilyConnection g c P i y q l)) z
  apply (hV.add (ContDiffAt.sum (fun i _ =>
    (heatFamilyDrift_contDiffAt n g c P z hP hz hmetric i).mul (hA0 i k l)))).sub
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (hInv i j).mul ((hD i j k l).add
    (ContDiffAt.sum (fun q _ => (hA0 j k q).mul (hA0 i q l))))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The fixed space of the actual scalar shifted resolvent is precisely the
constant functions on the connected manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarFixed_frameCompact
theorem scalarBaseResolvent_fixed_one :
    scalarBaseResolvent g o d (smoothScalarBaseL2 g (smoothScalarConst 1)) =
      smoothScalarBaseL2 g (smoothScalarConst 1) := by
  have hu : scalarBaseShiftedSolution g o d (smoothScalarBaseL2 g (smoothScalarConst 1)) =
      scalarH1One d := by
    apply ext_inner_right ℝ
    intro v
    rw [scalarBaseShiftedSolution_weak, scalarH1_inner_base]
    simp only [scalarH1Gradient_one, inner_zero_left, Finset.sum_const_zero, add_zero]
    change inner ℝ (smoothScalarBaseL2 g (smoothScalarConst 1)) (scalarH1BaseValue g o d v) =
      inner ℝ (scalarH1BaseValue g o d (smoothScalarToH1 d (smoothScalarConst 1)))
        (scalarH1BaseValue g o d v)
    rw [scalarH1BaseValue_smooth]
  change scalarH1BaseValue g o d (scalarBaseShiftedSolution g o d _) = _
  rw [hu]
  exact scalarH1BaseValue_smooth g o d (smoothScalarConst 1)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Higher integer regularity of the positive power needed by the Euler
source. The range condition is only on the support of the localization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set
open scoped SchwartzMap ENNReal LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "L2" => Lp ℝ 2 (volume : Measure V)
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)
local notation "D" => fun (i : Fin 4) (f : S) => ∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} f

/-- A positive bounded local power loses at most one of the available
integer Sobolev derivatives. Combined with the two-derivative elliptic gain,
this is the required ascending bootstrap. -/
theorem scalar_localized_integer_positive_power (n : ℕ) (hn : 2 ≤ n) :
    ∀ (u : L2) (χ : S), HasCompactSupport (χ : V → ℝ) →
      ∀ (a B q : ℝ), 0 < a → 0 ≤ B →
      MemSobolev ((n : ℝ) + 1) 2 (scalarComplexL2 u : T) →
      (∀ᵐ x ∂(volume : Measure V), x ∈ tsupport (χ : V → ℝ) → u x ∈ Icc a B) →
      ∃ v : L2, MemSobolev (n : ℝ) 2 (scalarComplexL2 v : T) ∧
        (v : V → ℝ) =ᵐ[volume] fun x => χ x * (u x) ^ q := by
  induction n, hn using Nat.le_induction with
  | base =>
    intro u χ hc a B q ha hB hu hrange
    apply scalar_localized_H2_positive_power u (hu.mono (by norm_num)) χ hc a B q ha hB
    filter_upwards [hrange] with x hx hχ
    exact hx (subset_tsupport (χ : V → ℝ) hχ)
  | succ n hn ih =>
    intro u χ hc a B q ha hB hu hrange
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have huLow : MemSobolev ((n : ℝ) + 1) 2 (scalarComplexL2 u : T) :=
      hu.mono (by push_cast; linarith)
    have hu2 : MemSobolev 2 2 (scalarComplexL2 u : T) :=
      huLow.mono (by linarith)
    have hderiv (i : Fin 4) := scalar_real_derivative_sobolev (n + 1) u hu i
    choose Du hDu hDuN using hderiv
    obtain ⟨v, _, hve, hDv⟩ := scalar_localized_positive_power_weak_derivative u hu2 Du hDu
      χ hc a B q ha hB hrange
    obtain ⟨w, hw, hwe⟩ := ih u χ hc a B q ha hB huLow hrange
    have hvw : v = w := Lp.ext (hve.trans hwe.symm)
    have hvN : MemSobolev (n : ℝ) 2 (scalarComplexL2 v : T) := by rwa [hvw]
    refine ⟨v, ?_, hve⟩
    have hvSucc : MemSobolev ((n : ℝ) + 1) 2 (scalarComplexL2 v : T) := by
      apply (scalar_memSobolev_succ_iff (n : ℝ) _).mpr
      refine ⟨hvN, fun i => ?_⟩
      have hs : tsupport ((D i χ : S) : V → ℝ) ⊆ tsupport (χ : V → ℝ) :=
        SchwartzMap.tsupport_lineDerivOp_subset (EuclideanSpace.basisFun (Fin 4) ℝ i) χ
      have hcD : HasCompactSupport ((D i χ : S) : V → ℝ) :=
        hc.of_isClosed_subset (isClosed_tsupport _) hs
      have hrD : ∀ᵐ x ∂(volume : Measure V),
          x ∈ tsupport ((D i χ : S) : V → ℝ) → u x ∈ Icc a B := by
        filter_upwards [hrange] with x hx hxs
        exact hx (hs hxs)
      obtain ⟨A, hA, hAe⟩ := ih u (D i χ) hcD a B q ha hB huLow hrD
      obtain ⟨P, hP, hPe⟩ := ih u χ hc a B (q - 1) ha hB huLow hrange
      obtain ⟨C, hC, hCe⟩ := scalar_real_integer_product_extra n hn P (Du i) hP
        (by simpa only [Nat.cast_add, Nat.cast_one] using hDuN i)
      obtain ⟨z, hz, hze⟩ := hDv i
      have he : z = A + q • C := by
        apply Lp.ext
        filter_upwards [hze, hAe, hPe, hCe, Lp.coeFn_add A (q • C), Lp.coeFn_smul q C]
          with x hz hA hP hC hadd hsmul
        rw [hz, hadd, Pi.add_apply, hsmul, Pi.smul_apply, smul_eq_mul, hA, hC, hP]
        ring
      rw [hz, he]
      exact scalar_real_sobolev_add (n : ℝ) A (q • C) hA
        (scalar_real_sobolev_smul (n : ℝ) q C hC)
    simpa only [Nat.cast_add, Nat.cast_one] using hvSucc

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite smooth extensions of the normal-coordinate coefficients.
They agree with the geometric operator near the center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalExtension.transport_neighborhood {n : ℕ}
    {g : SmoothMetric M} {o : FrameOrientation g} {e : FrameBundle g}
    (D : HeatNormalExtension n g o e) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r,
      (∀ i, ∑ j : Fin 4, D.a x i j * x j = x i) ∧
      (∀ j, ∑ i : Fin 4, D.a x i j * x i = x j) ∧
      fourHeatEikonalDefect (D.a x) x = 0 ∧
      fourHeatRadialTransport (D.a x) (D.b x) D.U x = 0 := by
  obtain ⟨r₁, hr₁, hT⟩ := heatNormalLeadingAmplitude_transport_neighborhood g o hRic e he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace),
      D.a x = (heatNormalMetric g o e x)⁻¹ ∧ D.b x = heatNormalDrift g o e x ∧
      D.U =ᶠ[𝓝 x] heatNormalLeadingAmplitude g o e ∧
      (heatNormalMetric g o e x).det ≠ 0 ∧ x ∈ ball 0 r₁ := by
    filter_upwards [D.a_near, D.b_near, D.U_near.eventuallyEq_nhds,
      heatNormalMetric_eventually_nondegenerate g o e, ball_mem_nhds (0 : FourSpace) hr₁]
      with x ha hb hU hd hx
    exact ⟨ha, hb, hU, hd, hx⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro x hx
  obtain ⟨ha, hb, hU, hd, hx₁⟩ := hball hx
  have hrow (i : Fin 4) : ∑ j : Fin 4, D.a x i j * x j = x i := by
    rw [ha]
    exact congrFun (heatNormalMetric_inverse_radial g o hRic e he x hd) i
  have hcol (j : Fin 4) : ∑ i : Fin 4, D.a x i j * x i = x j := by
    rw [ha]
    have hs (i : Fin 4) : (heatNormalMetric g o e x)⁻¹ i j =
        (heatNormalMetric g o e x)⁻¹ j i :=
      congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    simp_rw [hs]
    simpa only [ha] using hrow j
  refine ⟨hrow, hcol, ?_, ?_⟩
  · rw [ha]
    exact heatNormalMetric_eikonal g o hRic e he x hd
  · rw [fourHeatRadialTransport_germ _ _ hU, ha, hb]
    exact hT x hx₁

end
end PositiveEinsteinFour.Geometry
end


section

/-! Higher local Euler powers after dividing by the actual smooth positive density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff NNReal

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℝ)

theorem scalar_local_integer_power_source (n : ℕ) (hn : 2 ≤ n) (ρ b : V → ℝ)
    (w : Lp ℝ 2 (volume : Measure V))
    (heq : (fun y => ρ y * b y) =ᵐ[volume.restrict (ball (0 : V) 1)] w)
    (hreg : ∀ φ : 𝓢(V, ℂ), HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2) →
      MemSobolev ((n : ℝ) + 1) 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)))
    (hρ : ∀ y ∈ closedBall (0 : V) (1 / 2), ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y)
    (hρ0 : ∀ y ∈ closedBall (0 : V) (1 / 2), ρ y ≠ 0)
    (a B q : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hRange : ∀ x ∈ closedBall (0 : V) (1 / 2), b x ∈ Icc a B)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℝ))
    (hs : tsupport (ψ : V → ℝ) ⊆ ball 0 (1 / 2)) :
    ∃ v : Lp ℝ 2 (volume : Measure V), MemSobolev (n : ℝ) 2 (scalarComplexL2 v : T) ∧
      (v : V → ℝ) =ᵐ[volume] fun y => ψ y * (b y) ^ q := by
  obtain ⟨χ, hχ, hχc, hχs, hone⟩ := scalar_half_ball_cutoff_of_compact hc hs
  obtain ⟨z, hz2, hz⟩ := scalar_integer_density_division (n + 1) ρ b w heq
    (fun φ hc hs => by simpa only [Nat.cast_add, Nat.cast_one] using hreg φ hc hs) χ hχ hχc hχs
    (fun y hy => hρ y (ball_subset_closedBall (hχs hy)))
    (fun y hy => hρ0 y (ball_subset_closedBall (hχs hy)))
  obtain ⟨u, hu2, hu⟩ := scalar_real_integer_realization (n + 1) z hz2 (fun y => χ y * b y) hz
  have hru : ∀ᵐ x ∂(volume : Measure V), x ∈ tsupport (ψ : V → ℝ) → u x ∈ Icc a B := by
    filter_upwards [hu] with x hx hxs
    rw [hx, hone x hxs, one_mul]
    exact hRange x (ball_subset_closedBall (hs hxs))
  obtain ⟨v, hv2, hv⟩ := scalar_localized_integer_positive_power n hn u ψ hc a B q ha hB
    (by simpa only [Nat.cast_add, Nat.cast_one] using hu2) hru
  refine ⟨v, hv2, ?_⟩
  filter_upwards [hv, hu] with x hx hu
  rw [hx]
  by_cases hψ : ψ x = 0
  · simp only [hψ, zero_mul]
  · rw [hu, hone x (subset_tsupport (ψ : V → ℝ) hψ), one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact spatial slices of the lower order family coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatFamilyZero_slice (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ 2 P z) (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hframe : (P z).2.det ≠ 0) (hmetric : 0 < (heatFamilyMetric g c P z).det) :
    heatFamilyZero g c P z = fourHeatConnectionZero
      (heatFamilyMetric g c P z)⁻¹
      (fourHeatDensityDrift (fun x => (heatFamilyMetric g c P (x, z.2))⁻¹)
        (fun x => heatFamilyDensity g c P (x, z.2)) z.1)
      (heatTwoFormConnection g c (fun x => P (x, z.2)))
      (heatNormalPotential g c (fun x => P (x, z.2)) z.1) z.1 := by
  have hp := hP.differentiableAt (by norm_num)
  have hA (i : Fin 4) (k l : Fin 6) :
      DifferentiableAt ℝ (fun y => heatFamilyTwoFormConnection g c P i y k l) z :=
    (heatFamilyTwoFormConnection_contDiffAt 1 g c P z hP hz hframe i k l).differentiableAt one_ne_zero
  have he (i : Fin 4) (k l : Fin 6) :
      (fun x => heatFamilyTwoFormConnection g c P i (x, z.2) k l) =ᶠ[𝓝 z.1]
        (fun x => heatTwoFormConnection g c (fun y => P (y, z.2)) i x k l) := by
    have hi : Tendsto (fun x : FourSpace => (x, z.2)) (𝓝 z.1) (𝓝 z) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hi.eventually (hP.eventually (by simp))] with x hx
    exact congrArg (fun A : HeatMat6 => A k l)
      (heatFamilyTwoFormConnection_slice g c P (x, z.2) (hx.differentiableAt (by norm_num)) i)
  have hD (i j : Fin 4) (k l : Fin 6) :
      heatFamilyScalarPartial (fun y => heatFamilyTwoFormConnection g c P i y k l) j z =
        partialDeriv (fun y => heatTwoFormConnection g c (fun x => P (x, z.2)) i y k l) j z.1 := by
    rw [heatFamilyScalarPartial_slice _ z (hA i k l) j]
    exact fourHeat_partial_germ (he i k l) j
  have hb : heatFamilyDrift g c P z =
      fourHeatDensityDrift (fun x => (heatFamilyMetric g c P (x, z.2))⁻¹)
        (fun x => heatFamilyDensity g c P (x, z.2)) z.1 := by
    funext j
    exact heatFamilyDrift_slice g c P z hP hz hmetric j
  have hV : heatFamilyPotential g c P z =
      heatNormalPotential g c (fun x => P (x, z.2)) z.1 := rfl
  simp only [heatFamilyZero, fourHeatConnectionZero, hb, hV,
    heatFamilyTwoFormConnection_slice g c P z hp, hD]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite-regularity coefficients of the two-form operator in
normal coordinates and the radially parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.bundleFirst_radial_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ k l : Fin 6,
      (∑ i : Fin 4, x i * heatNormalBundleFirst D x i k l) = 0 := by
  filter_upwards [ball_mem_nhds (0 : FourSpace) D.radius_pos,
    heatNormalMetric_eventually_nondegenerate g o e] with x hx hd
  intro k l
  have h := D.bundleFirst_radial hRic he x hx hd
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    using congrArg (fun A : HeatMat6 => A k l) h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual finite-regularity coefficients of the one-form operator in
normal coordinates and the radially parallel frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.oneFirst_radial_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ k l : Fin 4,
      (∑ i : Fin 4, x i * heatNormalOneFirst D x i k l) = 0 := by
  filter_upwards [ball_mem_nhds (0 : FourSpace) D.radius_pos,
    heatNormalMetric_eventually_nondegenerate g o e] with x hx hd
  intro k l
  have h := D.oneFirst_radial hRic he x hx hd
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    using congrArg (fun A : Mat4 => A k l) h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The positive Euler source gains integer regularity from the actual localized solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)
local notation "S" => 𝓢(V, ℂ)
local notation "C2" => Lp ℂ 2 (volume : Measure V)

theorem scalar_local_integer_nonlinear_source (n : ℕ) (hn : 2 ≤ n) (ρ b : V → ℝ)
    (w : Lp ℝ 2 (volume : Measure V))
    (heq : (fun y => ρ y * b y) =ᵐ[volume.restrict (ball (0 : V) 1)] w)
    (hreg : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2) →
      MemSobolev ((n : ℝ) + 1) 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)))
    (hρ : ∀ y ∈ closedBall (0 : V) (1 / 2), ContDiffAt ℝ ∞ ρ y)
    (hρ0 : ∀ y ∈ closedBall (0 : V) (1 / 2), ρ y ≠ 0)
    (a B q A C : ℝ) (ha : 0 < a) (hB : 0 ≤ B)
    (hRange : ∀ x ∈ closedBall (0 : V) (1 / 2), b x ∈ Icc a B)
    (F : C2)
    (hF : (F : V → ℂ) =ᵐ[volume.restrict (ball (0 : V) (1 / 2))]
      fun y => (ρ y * (A * b y + C * (b y) ^ q) : ℝ))
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2)) :
    MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ ψ (F : T)) := by
  obtain ⟨η, hη, hηc, hηs, hone⟩ := scalar_half_ball_cutoff_of_compact hc hs
  have hinv (y : V) (hy : y ∈ closedBall (0 : V) (1 / 2)) :
      ContDiffAt ℝ ∞ (fun y => (ρ y)⁻¹) y := (hρ y hy).inv (hρ0 y hy)
  let ηS : 𝓢(V, ℝ) := hηc.toSchwartzMap hη
  have hηSs : tsupport (ηS : V → ℝ) ⊆ ball 0 (1 / 2) := hηs
  obtain ⟨v₁, hv₁, he₁⟩ := scalar_local_integer_power_source n hn ρ b w heq hreg hinv hρ0
    a B 1 ha hB hRange ηS hηc hηSs
  obtain ⟨vq, hvq, heq'⟩ := scalar_local_integer_power_source n hn ρ b w heq hreg hinv hρ0
    a B q ha hB hRange ηS hηc hηSs
  let z : C2 := (A : ℂ) • scalarComplexL2 v₁ + (C : ℂ) • scalarComplexL2 vq
  have hz : (z : T) = (A : ℂ) • (scalarComplexL2 v₁ : T) +
      (C : ℂ) • (scalarComplexL2 vq : T) := by
    change (Lp.toTemperedDistributionCLM ℂ volume 2) _ = _
    rw [map_add, map_smul, map_smul]
    rfl
  have hz2 : MemSobolev (n : ℝ) 2 (z : T) := by
    rw [hz]
    exact (hv₁.smul (A : ℂ)).add (hvq.smul (C : ℂ))
  let θ : S := scalarCutoffSchwartz η ρ hη hηc
    (fun y hy => hρ y (ball_subset_closedBall (hηs hy)))
  let Γ : S := SchwartzMap.smulLeftCLM ℂ θ ψ
  have hΓ (y : V) : Γ y = ((η y * ρ y : ℝ) : ℂ) * ψ y := by
    simp only [Γ, SchwartzMap.smulLeftCLM_apply θ.hasTemperateGrowth, smul_eq_mul]
    rfl
  have hzeq : (z : V → ℂ) =ᵐ[volume] fun y =>
      (A * (η y * b y) + C * (η y * (b y) ^ q) : ℝ) := by
    filter_upwards [Lp.coeFn_add ((A : ℂ) • scalarComplexL2 v₁)
        ((C : ℂ) • scalarComplexL2 vq),
      Lp.coeFn_smul (A : ℂ) (scalarComplexL2 v₁),
      Lp.coeFn_smul (C : ℂ) (scalarComplexL2 vq),
      scalarComplexL2_coe v₁, scalarComplexL2_coe vq, he₁, heq']
      with y hz ha hc h₁ hq hv₁ hvq
    change ((A : ℂ) • scalarComplexL2 v₁ + (C : ℂ) • scalarComplexL2 vq) y = _
    rw [hz]
    simp only [Pi.add_apply]
    rw [ha, hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h₁, hq, hv₁, hvq]
    simp only [ηS, Real.rpow_one, Complex.ofReal_add, Complex.ofReal_mul]
    rfl
  have hidentity : smulLeftCLM ℂ ψ (F : T) = smulLeftCLM ℂ Γ (z : T) := by
    ext φ
    simp only [smulLeftCLM_apply_apply, Lp.toTemperedDistribution_apply]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' isOpen_ball.measurableSet).mp hF, hzeq]
      with y hf hz
    simp only [SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth,
      SchwartzMap.smulLeftCLM_apply Γ.hasTemperateGrowth, smul_eq_mul, hΓ, hz]
    by_cases hy : ψ y = 0
    · simp only [hy, mul_zero, zero_mul]
    · have hys := subset_tsupport (ψ : V → ℂ) hy
      rw [hf (hs hys), hone y hys]
      simp only [one_mul, Complex.ofReal_add, Complex.ofReal_mul]
      ring
  rw [hidentity]
  exact scalar_memSobolev_schwartz_multiplier n Γ (z : T) hz2

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

theorem fourHeatRadialAverage_second_zero (m : ℕ) (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 2 f) (i j : Fin 4) :
    partialDeriv (partialDeriv (fourHeatRadialAverage m f) i) j 0 =
      partialDeriv (partialDeriv f i) j 0 / (m + 3 : ℝ) := by
  have he : partialDeriv (fourHeatRadialAverage m f) i =
      fourHeatRadialAverage (m + 1) (partialDeriv f i) :=
    funext (fun x => fourHeatRadialAverage_partial m f (hf.of_le (by norm_num)) x i)
  rw [he, fourHeatRadialAverage_partial_zero (m + 1) (partialDeriv f i)
    (fourHeat_partial_contDiff 1 f hf i) j]
  push_cast
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The family and geometric coefficient operators agree throughout a
common normal ball, including all differentiated lower order terms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatFamilyNormal_on_ball {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e))
    (r : ℝ) (hrD : r ≤ D.radius)
    (hP : ∀ x ∈ ball (0 : FourSpace) r, ContDiffAt ℝ 2 P (x, frameCoordinateState g c e))
    (hsource : ∀ x ∈ ball (0 : FourSpace) r,
      frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hdet : ∀ x ∈ ball (0 : FourSpace) r,
      0 < (heatFamilyMetric g c P (x, frameCoordinateState g c e)).det) :
    ∀ x ∈ ball (0 : FourSpace) r,
      (heatFamilyMetric g c P (x, frameCoordinateState g c e))⁻¹ = (heatNormalMetric g o e x)⁻¹ ∧
      heatFamilyDrift g c P (x, frameCoordinateState g c e) = heatNormalDrift g o e x ∧
      heatFamilyFirst g c P (x, frameCoordinateState g c e) = heatNormalBundleFirst D x ∧
      heatFamilyZero g c P (x, frameCoordinateState g c e) = heatNormalBundleZero D x ∧
      heatFamilyLeading g c P (x, frameCoordinateState g c e) = heatNormalLeadingAmplitude g o e x := by
  let q := frameCoordinateState g c e
  have hm (x : FourSpace) (hx : x ∈ ball 0 r) :
      heatFamilyMetric g c P (x, q) = heatNormalMetric g o e x :=
    D.metric_slice_eq P hpoint x (ball_subset_ball hrD hx)
      ((hP x hx).differentiableAt (by norm_num)) (hsource x hx)
  have hJ (x : FourSpace) (hx : x ∈ ball 0 r) :
      heatFamilyDensity g c P (x, q) = frameExponentialJacobian g o e x :=
    congrArg (fun A : Mat4 => Real.sqrt A.det) (hm x hx)
  have hc (x : FourSpace) (hx : x ∈ ball 0 r) : (P (x, q)).1 ∈ (chartAt FourSpace c).target := by
    simpa only [hpoint] using D.in_chart x (ball_subset_ball hrD hx)
  have hA (i : Fin 4) (x : FourSpace) (hx : x ∈ ball 0 r) :
      heatFamilyTwoFormConnection g c P i (x, q) = heatTwoFormConnection g c D.point i x := by
    rw [heatFamilyTwoFormConnection_slice g c P (x, q) ((hP x hx).differentiableAt (by norm_num)) i]
    rw [hpoint]
  have hb (x : FourSpace) (hx : x ∈ ball 0 r) :
      heatFamilyDrift g c P (x, q) = heatNormalDrift g o e x := by
    have hma : (fun y => (heatFamilyMetric g c P (y, q))⁻¹) =ᶠ[𝓝 x]
        (fun y => (heatNormalMetric g o e y)⁻¹) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      rw [hm y hy]
    have hj : (fun y => heatFamilyDensity g c P (y, q)) =ᶠ[𝓝 x]
        frameExponentialJacobian g o e := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact hJ y hy
    funext j
    rw [heatFamilyDrift_slice g c P (x, q) (hP x hx) (hc x hx) (hdet x hx) j]
    exact congrFun (fourHeatDensityDrift_germ hma hj) j
  intro x hx
  refine ⟨congrArg Inv.inv (hm x hx), hb x hx, ?_, ?_, ?_⟩
  · unfold heatFamilyFirst heatNormalBundleFirst
    rw [hm x hx]
    funext i
    congr 1
    funext j
    exact hA j x hx
  · have hframe : (P (x, q)).2.det ≠ 0 := by
      have hg := congrArg Matrix.det (D.orthonormal x (ball_subset_ball hrD hx))
      rw [hpoint] at hg
      simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
      change (P (x, q)).2.det * (metricInChart g c (P (x, q)).1).det * (P (x, q)).2.det = 1 at hg
      intro hz
      rw [hz] at hg
      norm_num at hg
    rw [heatFamilyZero_slice g c P (x, q) (hP x hx) (hc x hx) hframe (hdet x hx), hm x hx]
    have hb' : fourHeatDensityDrift (fun y => (heatFamilyMetric g c P (y, q))⁻¹)
        (fun y => heatFamilyDensity g c P (y, q)) x = heatNormalDrift g o e x := by
      funext j
      exact (heatFamilyDrift_slice g c P (x, q) (hP x hx) (hc x hx) (hdet x hx) j).symm.trans
        (congrFun (hb x hx) j)
    rw [hb']
    simp only [heatNormalBundleZero, hpoint]
    rfl
  · exact congrArg (fun a : ℝ => (Real.sqrt a)⁻¹) (hJ x hx)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The one-form coefficient family restricts to the actual normal operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatFamilyOneZero_slice (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ 2 P z) (hz : (P z).1 ∈ (chartAt FourSpace c).target)
    (hframe : (P z).2.det ≠ 0) (hmetric : 0 < (heatFamilyMetric g c P z).det) :
    heatFamilyOneZero g c P z = fourHeatOneConnectionZero
      (heatFamilyMetric g c P z)⁻¹
      (fourHeatDensityDrift (fun x => (heatFamilyMetric g c P (x, z.2))⁻¹)
        (fun x => heatFamilyDensity g c P (x, z.2)) z.1)
      (heatNormalFrameConnection g c (fun x => P (x, z.2)))
      (((3 : ℝ) • (1 : Mat4))) z.1 := by
  have hp := hP.differentiableAt (by norm_num)
  have hA (i : Fin 4) (k l : Fin 4) :
      DifferentiableAt ℝ (fun y => heatFamilyConnection g c P i y k l) z :=
    (heatFamilyConnection_contDiffAt 1 g c P z hP hz hframe i k l).differentiableAt one_ne_zero
  have he (i : Fin 4) (k l : Fin 4) :
      (fun x => heatFamilyConnection g c P i (x, z.2) k l) =ᶠ[𝓝 z.1]
        (fun x => heatNormalFrameConnection g c (fun y => P (y, z.2)) i x k l) := by
    have hi : Tendsto (fun x : FourSpace => (x, z.2)) (𝓝 z.1) (𝓝 z) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hi.eventually (hP.eventually (by simp))] with x hx
    exact congrArg (fun A : Mat4 => A k l)
      (heatFamilyConnection_slice g c P (x, z.2) (hx.differentiableAt (by norm_num)) i)
  have hD (i j : Fin 4) (k l : Fin 4) :
      heatFamilyScalarPartial (fun y => heatFamilyConnection g c P i y k l) j z =
        partialDeriv (fun y => heatNormalFrameConnection g c (fun x => P (x, z.2)) i y k l) j z.1 := by
    rw [heatFamilyScalarPartial_slice _ z (hA i k l) j]
    exact fourHeat_partial_germ (he i k l) j
  have hb : heatFamilyDrift g c P z =
      fourHeatDensityDrift (fun x => (heatFamilyMetric g c P (x, z.2))⁻¹)
        (fun x => heatFamilyDensity g c P (x, z.2)) z.1 := by
    funext j
    exact heatFamilyDrift_slice g c P z hP hz hmetric j
  simp only [heatFamilyOneZero, fourHeatOneConnectionZero, hb,
    heatFamilyConnection_slice g c P z hp, hD]


end
end PositiveEinsteinFour.Geometry
end


section

/-! One global finite-smooth family extends all actual normal
coefficients near a given frame, with a positive leading amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_heatFamilySmoothCoefficients (g : SmoothMetric M) (c : M)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace) (z₀ : HeatRadialFrameSpace)
    (hP : ContDiffAt ℝ 12 P z₀) (hz : (P z₀).1 ∈ (chartAt FourSpace c).target)
    (hframe : (P z₀).2.det ≠ 0) (hmetric : 0 < (heatFamilyMetric g c P z₀).det) :
    ∃ E : HeatFamilySmoothCoefficients,
      E.a =ᶠ[𝓝 z₀] (fun z => (heatFamilyMetric g c P z)⁻¹) ∧
      E.b =ᶠ[𝓝 z₀] heatFamilyDrift g c P ∧
      E.B =ᶠ[𝓝 z₀] heatFamilyFirst g c P ∧
      E.C =ᶠ[𝓝 z₀] heatFamilyZero g c P ∧
      E.U =ᶠ[𝓝 z₀] heatFamilyLeading g c P := by
  choose A hA hAc hAe using fun i j => heatFamily_scalar_extension 10
    (fun z => (heatFamilyMetric g c P z)⁻¹ i j) z₀
    (heatFamilyInverse_contDiffAt 10 g c P z₀ (hP.of_le (by norm_num)) hz hmetric.ne' i j)
  choose b hb hbc hbe using fun i => heatFamily_scalar_extension 10
    (fun z => heatFamilyDrift g c P z i) z₀
    (heatFamilyDrift_contDiffAt 10 g c P z₀ hP hz hmetric i)
  choose B hB hBc hBe using fun i k l => heatFamily_scalar_extension 10
    (fun z => heatFamilyFirst g c P z i k l) z₀
    (heatFamilyFirst_contDiffAt 10 g c P z₀ (hP.of_le (by norm_num)) hz hframe hmetric.ne' i k l)
  choose C hC hCc hCe using fun k l => heatFamily_scalar_extension 10
    (fun z => heatFamilyZero g c P z k l) z₀
    (heatFamilyZero_contDiffAt 10 g c P z₀ hP hz hframe hmetric k l)
  have hUpos : 0 < heatFamilyLeading g c P z₀ := inv_pos.mpr
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hmetric))
  obtain ⟨U, hU, hUp, hUe⟩ := heatFamily_positive_extension 10
    (heatFamilyLeading g c P) z₀
    (heatFamilyLeading_contDiffAt 10 g c P z₀ (hP.of_le (by norm_num)) hz hmetric) hUpos
  refine ⟨{
    a := fun z i j => A i j z
    b := fun z i => b i z
    B := fun z i k l => B i k l z
    C := fun z k l => C k l z
    U := U
    a_regular := hA
    b_regular := hb
    B_regular := hB
    C_regular := hC
    U_regular := hU
    U_pos := hUp }, ?_, ?_, ?_, ?_, hUe⟩
  · filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr (hAe i))] with z hz
    funext i j
    exact hz i j
  · filter_upwards [eventually_all.mpr hbe] with z hz
    funext i
    exact hz i
  · filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr
      (fun k => eventually_all.mpr (hBe i k)))] with z hz
    funext i k l
    exact hz i k l
  · filter_upwards [eventually_all.mpr (fun k => eventually_all.mpr (hCe k))] with z hz
    funext k l
    exact hz k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth extensions of the actual normal-frame bundle coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalBundleExtension.radial_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ k l : Fin 6,
      (∑ i : Fin 4, x i * E.B x i k l) = 0 := by
  filter_upwards [E.B_near, D.bundleFirst_radial_near hRic he] with x hx hrad
  simpa only [hx] using hrad

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite smooth extensions of the actual normal-frame bundle coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalOneExtension.radial_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ k l : Fin 4,
      (∑ i : Fin 4, x i * E.B x i k l) = 0 := by
  filter_upwards [E.B_near, D.oneFirst_radial_near hRic he] with x hx hrad
  simpa only [hx] using hrad

end
end PositiveEinsteinFour.Geometry
end


section

/-! All integer local regularity for the positive Euler equation. The initial
H2 gain is bootstrapped using the actual positive-power source and the local
elliptic estimate, on a fixed coordinate half ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_local_positive_Euler_all_orders
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c : S) (w : Lp ℝ 2 (volume : Measure V))
    (hw : MemSobolev 1 2 (scalarComplexL2 w : T))
    (hbase : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2) →
      MemSobolev 2 2 (M φ (scalarComplexL2 w : T)))
    (ρ u : V → ℝ)
    (heq : (fun y => ρ y * u y) =ᵐ[volume.restrict (ball (0 : V) 1)] w)
    (hρ : ∀ y ∈ closedBall (0 : V) (1 / 2), ContDiffAt ℝ ∞ ρ y)
    (hρ0 : ∀ y ∈ closedBall (0 : V) (1 / 2), ρ y ≠ 0)
    (l B q A C : ℝ) (hl : 0 < l) (hB : 0 ≤ B)
    (hRange : ∀ x ∈ closedBall (0 : V) (1 / 2), u x ∈ Icc l B)
    (F : Lp ℂ 2 (volume : Measure V))
    (hF : (F : V → ℂ) =ᵐ[volume.restrict (ball (0 : V) (1 / 2))]
      fun y => (ρ y * (A * u y + C * (u y) ^ q) : ℝ))
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2) →
      (scalarPerturbedOperator a b (scalarComplexL2 w : T) - (scalarComplexL2 w : T) -
        M c (scalarComplexL2 w : T)) ψ = (F : T) ψ) :
    ∀ n : ℕ, ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2) →
      MemSobolev (n : ℝ) 2 (M φ (scalarComplexL2 w : T)) := by
  let W : T := scalarComplexL2 w
  let O : T := scalarPerturbedOperator a b W - W - M c W
  have hOF (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
      (hs : tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2)) : M ψ O = M ψ (F : T) :=
    scalar_localize_eq_of_tests (ball 0 (1 / 2)) O (F : T) htest ψ hc hs
  have hsource2 (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
      (hs : tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2)) : MemSobolev 2 2 (M ψ O) := by
    rw [hOF ψ hc hs]
    exact scalar_local_H2_nonlinear_source ρ u w heq hbase hρ hρ0 l B q A C hl hB hRange F hF ψ hc hs
  have hreg : ∀ k : ℕ, ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2) →
      MemSobolev ((k : ℝ) + 4) 2 (M φ W) := by
    intro k
    induction k with
    | zero =>
      intro φ hc hs
      have h := scalar_half_open_integer_forcing_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall
        2 c W hw hsource2 φ hc hs
      norm_num only [Nat.cast_zero, Nat.cast_ofNat, zero_add] at h ⊢
      exact h
    | succ k ih =>
      intro φ hc hs
      have hsource (ψ : S) (hψc : HasCompactSupport (ψ : V → ℂ))
          (hψs : tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2)) :
          MemSobolev ((k + 3 : ℕ) : ℝ) 2 (M ψ O) := by
        rw [hOF ψ hψc hψs]
        apply scalar_local_integer_nonlinear_source (k + 3) (by omega) ρ u w heq
          (fun χ hχc hχs => ?_) hρ hρ0 l B q A C hl hB hRange F hF ψ hψc hψs
        have he : ((k + 3 : ℕ) : ℝ) + 1 = (k : ℝ) + 4 := by
          push_cast
          ring
        rw [he]
        exact ih χ hχc hχs
      have h := scalar_half_open_integer_forcing_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall
        (k + 3) c W hw hsource φ hc hs
      have he : (k.succ : ℝ) + 4 = ((k + 3 : ℕ) : ℝ) + 2 := by
        push_cast
        ring
      rw [he]
      exact h
  intro n φ hc hs
  exact (hreg n φ hc hs).mono (by linarith)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rough solution operator preserves the two Hodge summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormH1HodgeIsometry : TwoFormH1 o →ₗᵢ[ℝ] TwoFormH1 o where
  toLinearMap := twoFormH1Hodge.toLinearMap
  norm_map' := twoFormH1Hodge_norm

theorem twoFormH1Hodge_inner (u v : TwoFormH1 o) :
    inner ℝ (twoFormH1Hodge u) (twoFormH1Hodge v) = inner ℝ u v :=
  twoFormH1HodgeIsometry.inner_map_map u v

theorem twoFormH1Hodge_selfAdjoint (u v : TwoFormH1 o) :
    inner ℝ (twoFormH1Hodge u) v = inner ℝ u (twoFormH1Hodge v) := by
  have h := twoFormH1Hodge_inner u (twoFormH1Hodge v)
  rw [twoFormH1Hodge_involutive v] at h
  exact h

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

theorem fourHeatWeightedRadialAverage_second_zero (m : ℕ) (U F : FourSpace → ℝ)
    (hU : ContDiff ℝ 2 U) (hF : ContDiff ℝ 2 F) (hU0 : ∀ x, U x ≠ 0) (i j : Fin 4) :
    partialDeriv (partialDeriv (fourHeatWeightedRadialAverage m U F) i) j 0 =
      partialDeriv (partialDeriv U i) j 0 * ((F 0 / U 0) / (m + 1 : ℝ)) +
      partialDeriv U i 0 * (partialDeriv (fun x => F x / U x) j 0 / (m + 2 : ℝ)) +
      partialDeriv U j 0 * (partialDeriv (fun x => F x / U x) i 0 / (m + 2 : ℝ)) +
      U 0 * (partialDeriv (partialDeriv (fun x => F x / U x) i) j 0 / (m + 3 : ℝ)) := by
  have hQ : ContDiff ℝ 2 (fun y => F y / U y) := hF.div hU hU0
  have hR := fourHeatRadialAverage_preserves_contDiff 2 m _ hQ
  change partialDeriv (partialDeriv
    (fun x => U x * fourHeatRadialAverage m (fun y => F y / U y) x) i) j 0 = _
  rw [scalar_partial_second_product_at U (fourHeatRadialAverage m (fun y => F y / U y))
    0 hU.contDiffAt hR.contDiffAt i j,
    fourHeatRadialAverage_zero,
    fourHeatRadialAverage_partial_zero m _ (hQ.of_le (by norm_num)),
    fourHeatRadialAverage_partial_zero m _ (hQ.of_le (by norm_num)),
    fourHeatRadialAverage_second_zero m _ hQ]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The joint geometric coefficients have exactly the geometric normal germs,
including the derivatives in the drift and connection potential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatFamilyNormal_germs {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 2 P (0, frameCoordinateState g c e))
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e)) :
    ((fun x => (heatFamilyMetric g c P (x, frameCoordinateState g c e))⁻¹)
      =ᶠ[𝓝 0] (fun x => (heatNormalMetric g o e x)⁻¹)) ∧
    ((fun x => heatFamilyDrift g c P (x, frameCoordinateState g c e))
      =ᶠ[𝓝 0] heatNormalDrift g o e) ∧
    ((fun x => heatFamilyFirst g c P (x, frameCoordinateState g c e))
      =ᶠ[𝓝 0] heatNormalBundleFirst D) ∧
    ((fun x => heatFamilyZero g c P (x, frameCoordinateState g c e))
      =ᶠ[𝓝 0] heatNormalBundleZero D) ∧
    ((fun x => heatFamilyLeading g c P (x, frameCoordinateState g c e))
      =ᶠ[𝓝 0] heatNormalLeadingAmplitude g o e) := by
  let q := frameCoordinateState g c e
  have hi : Tendsto (fun x : FourSpace => (x, q)) (𝓝 0) (𝓝 (0, q)) :=
    continuousAt_id.prodMk continuousAt_const
  have hexp : (fun x => (P (x, q)).1) =ᶠ[𝓝 0]
      (fun x => chartAt FourSpace c (frameExponential g o e x)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    simpa only [hpoint] using D.exponential x hx
  have hm := heatFamilyMetric_exponential_germ g o c e he P (hP.of_le (by norm_num)) hexp
  have ha : (fun x => (heatFamilyMetric g c P (x, q))⁻¹) =ᶠ[𝓝 0]
      (fun x => (heatNormalMetric g o e x)⁻¹) := hm.mono fun x hx => congrArg Inv.inv hx
  have hJ := heatFamilyDensity_exponential_germ g o c e he P (hP.of_le (by norm_num)) hexp
  have hU := heatFamilyLeading_exponential_germ g o c e he P (hP.of_le (by norm_num)) hexp
  have hr := hi.eventually (hP.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hc : ∀ᶠ x in 𝓝 (0 : FourSpace), (P (x, q)).1 ∈ (chartAt FourSpace c).target := by
    filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    simpa only [hpoint] using D.in_chart x hx
  have hf : ∀ᶠ x in 𝓝 (0 : FourSpace), (P (x, q)).2.det ≠ 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    have hg := congrArg Matrix.det (D.orthonormal x hx)
    rw [hpoint] at hg
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
    change (P (x, q)).2.det * (metricInChart g c (P (x, q)).1).det *
      (P (x, q)).2.det = 1 at hg
    intro hz
    rw [hz] at hg
    norm_num at hg
  have hmp : ∀ᶠ x in 𝓝 (0 : FourSpace), 0 < (heatFamilyMetric g c P (x, q)).det := by
    have hzero : (heatNormalMetric g o e 0).det = 1 := by
      rw [heatNormalMetric_zero, Matrix.det_one]
    have hcont : ContinuousAt (heatNormalMetric g o e) 0 :=
      continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
        (heatNormalMetric_smoothAt_zero g o e i j).continuousAt
    have hdet : ContinuousAt (fun x => (heatNormalMetric g o e x).det) 0 :=
      continuous_id.matrix_det.continuousAt.comp hcont
    have hn : ∀ᶠ x in 𝓝 (0 : FourSpace), 0 < (heatNormalMetric g o e x).det :=
      hdet.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by rw [hzero]; norm_num))
    filter_upwards [hm, hn] with x hx hpos
    change heatFamilyMetric g c P (x, q) = heatNormalMetric g o e x at hx
    rw [hx]
    exact hpos
  have hb : (fun x => heatFamilyDrift g c P (x, q)) =ᶠ[𝓝 0] heatNormalDrift g o e := by
    filter_upwards [hr, hc, hmp, ha.eventuallyEq_nhds, hJ.eventuallyEq_nhds]
      with x hx hcx hmx hax hJx
    funext j
    rw [heatFamilyDrift_slice g c P (x, q) hx hcx hmx j]
    exact congrFun (fourHeatDensityDrift_germ hax hJx) j
  have hA (i : Fin 4) : (fun x => heatFamilyTwoFormConnection g c P i (x, q))
      =ᶠ[𝓝 0] heatTwoFormConnection g c D.point i := by
    filter_upwards [hr] with x hx
    rw [heatFamilyTwoFormConnection_slice g c P (x, q) (hx.differentiableAt (by norm_num)) i]
    rw [hpoint]
  have hAA : ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ i : Fin 4,
      (fun y => heatFamilyTwoFormConnection g c P i (y, q)) =ᶠ[𝓝 x]
        heatTwoFormConnection g c D.point i :=
    eventually_all.mpr (fun i => (hA i).eventuallyEq_nhds)
  refine ⟨ha, hb, ?_, ?_, hU⟩
  · filter_upwards [hr, ha, hAA] with x hx hax hAx
    rw [heatFamilyFirst_slice g c P (x, q) (hx.differentiableAt (by norm_num))]
    funext i
    change fourHeatConnectionFirst _ _ i = fourHeatConnectionFirst _ _ i
    rw [hax]
    congr 1
    funext j
    exact ((hAx j).self_of_nhds).symm.trans
      (heatFamilyTwoFormConnection_slice g c P (x, q) (hx.differentiableAt (by norm_num)) j)
      |>.symm
  · filter_upwards [hr, hc, hf, hmp, ha, hb, hAA] with x hx hcx hfx hmx hax hbx hAx
    rw [heatFamilyZero_slice g c P (x, q) hx hcx hfx hmx]
    have hb' : fourHeatDensityDrift (fun y => (heatFamilyMetric g c P (y, q))⁻¹)
        (fun y => heatFamilyDensity g c P (y, q)) x = heatNormalDrift g o e x := by
      funext j
      exact (heatFamilyDrift_slice g c P (x, q) hx hcx hmx j).symm.trans (congrFun hbx j)
    rw [hax, hb']
    have hAs (i : Fin 4) : heatTwoFormConnection g c (fun y => P (y, q)) i
        =ᶠ[𝓝 x] heatTwoFormConnection g c D.point i := by rw [hpoint]
    rw [fourHeatConnectionZero_germ _ _ _ hAs]
    simp only [heatNormalBundleZero, hpoint]
    rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual one-form coefficient agreement on the full common normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatFamilyOneNormal_on_ball {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e))
    (r : ℝ) (hrD : r ≤ D.radius)
    (hP : ∀ x ∈ ball (0 : FourSpace) r, ContDiffAt ℝ 2 P (x, frameCoordinateState g c e))
    (hsource : ∀ x ∈ ball (0 : FourSpace) r,
      frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hdet : ∀ x ∈ ball (0 : FourSpace) r,
      0 < (heatFamilyMetric g c P (x, frameCoordinateState g c e)).det) :
    ∀ x ∈ ball (0 : FourSpace) r,
      heatFamilyOneFirst g c P (x, frameCoordinateState g c e) = heatNormalOneFirst D x ∧
      heatFamilyOneZero g c P (x, frameCoordinateState g c e) = heatNormalOneZero D x := by
  let q := frameCoordinateState g c e
  have hraw := heatFamilyNormal_on_ball D P hpoint r hrD hP hsource hdet
  have hc (x : FourSpace) (hx : x ∈ ball 0 r) : (P (x, q)).1 ∈ (chartAt FourSpace c).target := by
    simpa only [hpoint] using D.in_chart x (ball_subset_ball hrD hx)
  have hA (i : Fin 4) (x : FourSpace) (hx : x ∈ ball 0 r) :
      heatFamilyConnection g c P i (x, q) = heatNormalFrameConnection g c D.point i x := by
    rw [heatFamilyConnection_slice g c P (x, q) ((hP x hx).differentiableAt (by norm_num)) i, hpoint]
  intro x hx
  constructor
  · unfold heatFamilyOneFirst heatNormalOneFirst
    rw [(hraw x hx).1]
    funext i
    congr 1
    funext j
    exact hA j x hx
  · have hframe : (P (x, q)).2.det ≠ 0 := by
      have hg := congrArg Matrix.det (D.orthonormal x (ball_subset_ball hrD hx))
      rw [hpoint] at hg
      simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
      change (P (x, q)).2.det * (metricInChart g c (P (x, q)).1).det * (P (x, q)).2.det = 1 at hg
      intro hz
      rw [hz] at hg
      norm_num at hg
    rw [heatFamilyOneZero_slice g c P (x, q) (hP x hx) (hc x hx) hframe (hdet x hx), (hraw x hx).1]
    have hb : fourHeatDensityDrift (fun y => (heatFamilyMetric g c P (y, q))⁻¹)
        (fun y => heatFamilyDensity g c P (y, q)) x = heatNormalDrift g o e x := by
      funext j
      exact (heatFamilyDrift_slice g c P (x, q) (hP x hx) (hc x hx) (hdet x hx) j).symm.trans
        (congrFun (hraw x hx).2.1 j)
    rw [hb]
    simp only [heatNormalOneZero, hpoint]
    rfl

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

theorem HeatNormalExtension.scalarAmplitude_transport (E : HeatNormalExtension 10 g o e)
    (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r,
      fourHeatEikonalDefect (E.a x) x = 0 ∧
      fourHeatRadialTransport (E.a x) (E.b x) (E.scalarAmplitude 0) x = 0 ∧
      ∀ m ≤ 2, fourHeatRadialTransport (E.a x) (E.b x) (E.scalarAmplitude (m + 1)) x +
        (m + 1 : ℝ) * E.scalarAmplitude (m + 1) x =
        -fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarAmplitude m) x := by
  obtain ⟨r, hr, hT⟩ := E.transport_neighborhood hRic he
  refine ⟨r, hr, ?_⟩
  intro x hx
  obtain ⟨hrow, hcol, hE, hU⟩ := hT x hx
  refine ⟨hE, hU, ?_⟩
  intro m hm
  exact fourHeatCoefficient_transport m E.a E.b (fun _ => 0) E.U x
    (E.U_regular.of_le (by norm_num)) (fun y => (E.U_pos y).ne')
    (fun i j => (E.a_regular i j).of_le (by norm_num))
    (fun i => (E.b_regular i).of_le (by norm_num)) contDiff_const
    ((E.scalarAmplitude_regular m (by omega)).of_le (by norm_num)) hrow hcol hU

theorem HeatNormalExtension.scalarParametrix_residual (E : HeatNormalExtension 10 g o e)
    (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ),
      deriv (fun s => E.scalarParametrix s x) t +
        fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x =
      fourHeatGaussian t x * t ^ 3 *
        fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarAmplitude 3) x := by
  obtain ⟨r, hr, hT⟩ := E.scalarAmplitude_transport hRic he
  refine ⟨r, hr, ?_⟩
  intro x hx t ht
  obtain ⟨hE, h0, hnext⟩ := hT x hx
  apply fourHeatPolynomial_gaussian_residual _ _ _ _
    (fun m => (E.scalarAmplitude_regular m (by omega)).of_le (by norm_num)) t ht x hE h0
  · simpa using hnext 0 (by omega)
  · convert hnext 1 (by omega) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  · convert hnext 2 (by omega) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Remove the single inverse-time factor from the cutoff commutator.
The resulting coefficient is continuous also at time zero. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatScaledCommutator_identity (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → HeatMat6)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 6 → ℝ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun y => u m y q)) (t : ℝ) (ht : 0 < t)
    (x : FourSpace) (k : Fin 6) :
    fourHeatLocalOperator (a x) (b x) 0 χ x *
        (fourHeatGaussian t x * fourHeatBundlePolynomial u t x k) -
      2 * (∑ i, ∑ j, a x i j * partialDeriv χ i x *
        partialDeriv (fun y => fourHeatGaussian t y * fourHeatBundlePolynomial u t y k) j x) +
      (∑ i, ∑ q, B x i k q * partialDeriv χ i x *
        (fourHeatGaussian t x * fourHeatBundlePolynomial u t x q)) =
      (fourHeatGaussian t x / t) * fourHeatScaledCommutator a b B χ u t x k := by
  have hP (q : Fin 6) : DifferentiableAt ℝ (fun y => fourHeatBundlePolynomial u t y q) x :=
    ((fourHeatPolynomial_contDiff (fun m y => u m y q) (fun m => hu m q) t).differentiable
      (by norm_num)).differentiableAt
  simp_rw [fourHeatGaussian_amplitude_partial_at t ht.ne' _ x (hP k)]
  unfold fourHeatScaledCommutator
  have hg : (∑ i, ∑ j, a x i j * partialDeriv χ i x *
      (fourHeatGaussian t x * (partialDeriv (fun y => fourHeatBundlePolynomial u t y k) j x -
        x j / (2 * t) * fourHeatBundlePolynomial u t x k))) =
      (fourHeatGaussian t x / t) * (∑ i, ∑ j, a x i j * partialDeriv χ i x *
        (t * partialDeriv (fun y => fourHeatBundlePolynomial u t y k) j x -
          x j / 2 * fourHeatBundlePolynomial u t x k)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have hB : (∑ i, ∑ q, B x i k q * partialDeriv χ i x *
      (fourHeatGaussian t x * fourHeatBundlePolynomial u t x q)) =
      fourHeatGaussian t x * (∑ i, ∑ q, B x i k q * partialDeriv χ i x *
        fourHeatBundlePolynomial u t x q) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hg, hB]
  field_simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The joint one-form geometry has the actual normal-frame coefficient germs. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatFamilyOneNormal_germs {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 2 P (0, frameCoordinateState g c e))
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e)) :
    ((fun x => heatFamilyOneFirst g c P (x, frameCoordinateState g c e))
      =ᶠ[𝓝 0] heatNormalOneFirst D) ∧
    ((fun x => heatFamilyOneZero g c P (x, frameCoordinateState g c e))
      =ᶠ[𝓝 0] heatNormalOneZero D) := by
  let q := frameCoordinateState g c e
  have hi : Tendsto (fun x : FourSpace => (x, q)) (𝓝 0) (𝓝 (0, q)) :=
    continuousAt_id.prodMk continuousAt_const
  have hG := heatFamilyNormal_germs D he P hP hpoint
  have hr := hi.eventually (hP.eventually (by simp))
  have hc : ∀ᶠ x in 𝓝 (0 : FourSpace), (P (x, q)).1 ∈ (chartAt FourSpace c).target := by
    filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    simpa only [hpoint] using D.in_chart x hx
  have hf : ∀ᶠ x in 𝓝 (0 : FourSpace), (P (x, q)).2.det ≠ 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    have hg := congrArg Matrix.det (D.orthonormal x hx)
    rw [hpoint] at hg
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
    change (P (x, q)).2.det * (metricInChart g c (P (x, q)).1).det *
      (P (x, q)).2.det = 1 at hg
    intro hz
    rw [hz] at hg
    norm_num at hg
  have hA (i : Fin 4) : (fun x => heatFamilyConnection g c P i (x, q))
      =ᶠ[𝓝 0] heatNormalFrameConnection g c D.point i := by
    filter_upwards [hr] with x hx
    rw [heatFamilyConnection_slice g c P (x, q) (hx.differentiableAt (by norm_num)) i, hpoint]
  have hAA := eventually_all.mpr (fun i => (hA i).eventuallyEq_nhds)
  constructor
  · filter_upwards [hG.1, eventually_all.mpr hA] with x ha hAx
    unfold heatFamilyOneFirst heatNormalOneFirst
    rw [ha]
    funext i
    congr 1
    funext j
    exact hAx j
  · filter_upwards [hr, hc, hf, hG.1, hG.2.1, hAA] with x hx hcx hfx hax hbx hAx
    have hp (i : Fin 4) (k l : Fin 4) :
        DifferentiableAt ℝ (fun z => heatFamilyConnection g c P i z k l) (x, q) :=
      (heatFamilyConnection_contDiffAt 1 g c P (x, q) hx hcx hfx i k l).differentiableAt one_ne_zero
    have hv (i : Fin 4) : heatFamilyConnection g c P i (x, q) =
        heatNormalFrameConnection g c D.point i x := (hAx i).self_of_nhds
    have hd (i j k l : Fin 4) :
        heatFamilyScalarPartial (fun z => heatFamilyConnection g c P i z k l) j (x, q) =
          partialDeriv (fun y => heatNormalFrameConnection g c D.point i y k l) j x := by
      rw [heatFamilyScalarPartial_slice _ (x, q) (hp i k l) j]
      exact fourHeat_partial_germ ((hAx i).mono fun y hy => congrArg (fun A : Mat4 => A k l) hy) j
    dsimp only [q] at hv hd
    simp only [heatFamilyOneZero, heatNormalOneZero, fourHeatOneConnectionZero,
      hax, hbx, hv, hd]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first four actual normal-frame matrix heat amplitudes and their
transport equations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalBundleExtension.amplitude_transport {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r,
      (∀ k l, (∑ i : Fin 4, x i * E.B x i k l) = 0) ∧
      fourHeatEikonalDefect (E.base.a x) x = 0 ∧
      (∀ m ≤ 2, ∀ k l,
        fourHeatRadialTransport (E.base.a x) (E.base.b x)
          (fun y => E.amplitude (m + 1) y k l) x +
          (m + 1 : ℝ) * E.amplitude (m + 1) x k l =
        -fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => E.amplitude m y q l) x k) := by
  obtain ⟨s, hs, hT⟩ := E.base.transport_neighborhood hRic he
  have hn := (E.radial_near hRic he).and (ball_mem_nhds (0 : FourSpace) hs)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro x hx
  obtain ⟨hrad, hxs⟩ := hball hx
  obtain ⟨hrow, hcol, hEik, hTU⟩ := hT x hxs
  refine ⟨hrad, hEik, ?_⟩
  intro m hm k l
  exact fourHeatBundleCoefficient_transport m E.base.a E.base.b E.B E.C E.base.U x
    (E.base.U_regular.of_le (by norm_num)) (fun y => (E.base.U_pos y).ne')
    (fun i j => (E.base.a_regular i j).of_le (by norm_num))
    (fun i => (E.base.b_regular i).of_le (by norm_num))
    (fun i k l => (E.B_regular i k l).of_le (by norm_num))
    (fun k l => (E.C_regular k l).of_le (by norm_num))
    (fun k l => (E.amplitude_regular m (by omega) k l).of_le (by norm_num))
    hrow hcol hTU k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The first four actual normal-frame matrix heat amplitudes and their
transport equations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalOneExtension.amplitude_transport {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r,
      (∀ k l, (∑ i : Fin 4, x i * E.B x i k l) = 0) ∧
      fourHeatEikonalDefect (E.base.a x) x = 0 ∧
      (∀ m ≤ 2, ∀ k l,
        fourHeatRadialTransport (E.base.a x) (E.base.b x)
          (fun y => E.amplitude (m + 1) y k l) x +
          (m + 1 : ℝ) * E.amplitude (m + 1) x k l =
        -fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => E.amplitude m y q l) x k) := by
  obtain ⟨s, hs, hT⟩ := E.base.transport_neighborhood hRic he
  have hn := (E.radial_near hRic he).and (ball_mem_nhds (0 : FourSpace) hs)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro x hx
  obtain ⟨hrad, hxs⟩ := hball hx
  obtain ⟨hrow, hcol, hEik, hTU⟩ := hT x hxs
  refine ⟨hrad, hEik, ?_⟩
  intro m hm k l
  exact fourHeatOneCoefficient_transport m E.base.a E.base.b E.B E.C E.base.U x
    (E.base.U_regular.of_le (by norm_num)) (fun y => (E.base.U_pos y).ne')
    (fun i j => (E.base.a_regular i j).of_le (by norm_num))
    (fun i => (E.base.b_regular i).of_le (by norm_num))
    (fun i k l => (E.B_regular i k l).of_le (by norm_num))
    (fun k l => (E.C_regular k l).of_le (by norm_num))
    (fun k l => (E.amplitude_regular m (by omega) k l).of_le (by norm_num))
    hrow hcol hTU k l

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

theorem HeatNormalFrameData.frame_connection_half_curvature
    {f : OrthonormalFrame g c} (D : HeatNormalFrameData g o c ⟨c, f⟩)
    (i j k l : Fin 4) :
    partialDeriv (fun x => heatNormalFrameConnection g c D.point j x k l) i 0 =
      (1 / 2 : ℝ) * curvatureEndomorphism (frameCurvature g c f) i j k l := by
  have hs := D.frame_connection_first_jet i j k l
  have hc := congrArg (fun A : Mat4 => A k l) (D.frame_connection_curvature_intrinsic i j)
  change partialDeriv (fun x => heatNormalFrameConnection g c D.point j x k l) i 0 -
    partialDeriv (fun x => heatNormalFrameConnection g c D.point i x k l) j 0 = _ at hc
  linarith

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-frame bundle parametrix through order three. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneParametrix_residual {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (hRic : RicciThree g) (he : e ∈ o.positive) :
    ∃ r > (0 : ℝ), ∀ x ∈ ball 0 r, ∀ t > (0 : ℝ), ∀ k l : Fin 4,
      deriv (fun s => heatNormalOneParametrix E s x k l) t +
        fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalOneFirst D x) (heatNormalOneZero D x)
          (fun y q => heatNormalOneParametrix E t y q l) x k =
      fourHeatGaussian t x * t ^ 3 *
        fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalOneFirst D x) (heatNormalOneZero D x)
          (fun y q => E.amplitude 3 y q l) x k := by
  obtain ⟨s, hs, htrans⟩ := E.amplitude_transport hRic he
  obtain ⟨s', hs', hbase⟩ := E.base.transport_neighborhood hRic he
  have hn : ∀ᶠ x in 𝓝 (0 : FourSpace),
      E.base.a x = (heatNormalMetric g o e x)⁻¹ ∧ E.base.b x = heatNormalDrift g o e x ∧
      E.B x = heatNormalOneFirst D x ∧ E.C x = heatNormalOneZero D x ∧
      x ∈ ball 0 s ∧ x ∈ ball 0 s' := by
    filter_upwards [E.base.a_near, E.base.b_near, E.B_near, E.C_near,
      ball_mem_nhds (0 : FourSpace) hs, ball_mem_nhds (0 : FourSpace) hs']
      with x ha hb hB hC hx hx'
    exact ⟨ha, hb, hB, hC, hx, hx'⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro x hx t ht k l
  obtain ⟨ha, hb, hB, hC, hxs, hxs'⟩ := hball hx
  obtain ⟨hrad, hEik, hnext⟩ := htrans x hxs
  have hTU := (hbase x hxs').2.2.2
  have hreg (m : Fin 4) (q : Fin 4) : ContDiff ℝ 2 (fun y => E.amplitude m y q l) :=
    (E.amplitude_regular m (by omega) q l).of_le (by norm_num)
  have hzero (q : Fin 4) : fourHeatRadialTransport (E.base.a x) (E.base.b x)
      (fun y => E.amplitude 0 y q l) x = 0 := by
    by_cases hql : q = l
    · subst q
      simpa [HeatNormalOneExtension.amplitude, fourHeatOneCoefficient] using hTU
    · have hz : (fun y => E.amplitude 0 y q l) = fun _ => (0 : ℝ) := by
        funext y
        simp [HeatNormalOneExtension.amplitude, fourHeatOneCoefficient, hql]
      rw [hz]
      have hc := fourHeatRadialTransport_const_mul (E.base.a x) (E.base.b x) 0 E.base.U x
      simpa only [zero_mul] using hc
  have h := fourHeatOnePolynomial_gaussian_residual (E.base.a x) (E.base.b x)
    (E.B x) (E.C x) (fun m y q => E.amplitude m y q l) hreg t ht x hrad hEik hzero
    (by intro q; simpa using hnext 0 (by omega) q l)
    (by intro q; convert hnext 1 (by omega) q l using 1 <;> norm_num)
    (by intro q; convert hnext 2 (by omega) q l using 1 <;> norm_num) k
  rw [ha, hb, hB, hC] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial first jet on two-forms is the actual curvature action,
including the sign imposed by covariant tensor slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heatTwoFormConnectionMatrix_curvature (R : CovariantCoordinates 4)
    (hl : ∀ i j k l, R ![i,j,l,k] = -R ![i,j,k,l]) (i j : Fin 4) :
    heatTwoFormConnectionMatrix (curvatureEndomorphism (fun a b c d => R ![a,b,c,d]) i j) =
      twoFormConnectionCurvatureMatrix R i j := by
  have hm : curvatureEndomorphism (fun a b c d => R ![a,b,c,d]) i j =
      -(fun k l => R ![i,j,k,l]) := by
    ext k l
    exact hl i j k l
  rw [hm]
  have hn : heatTwoFormConnectionMatrix (-(fun k l => R ![i,j,k,l] : Mat4)) =
      -heatTwoFormConnectionMatrix (fun k l => R ![i,j,k,l]) :=
    heatConnectionMatrixLinear.map_neg _
  rw [hn]
  exact congrArg (fun A : HeatMat6 => -A)
    (heatTwoFormConnectionMatrix_infinitesimal (fun k l => R ![i,j,k,l]))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem HeatNormalFrameData.twoForm_connection_half_curvature
    {f : OrthonormalFrame g c} (D : HeatNormalFrameData g o c ⟨c, f⟩)
    (i j : Fin 4) (k l : Fin 6) :
    partialDeriv (fun x => heatTwoFormConnection g c D.point j x k l) i 0 =
      (1 / 2 : ℝ) * twoFormConnectionCurvatureMatrix
        (twoFormMetricCurvatureTensor g (⟨c, f⟩ : FrameBundle g)) i j k l := by
  change partialDeriv (fun x => heatTwoFormConnectionMatrix
    (heatNormalFrameConnection g c D.point j x) k l) i 0 = _
  rw [heatTwoFormConnectionMatrix_partial _ 0
    (fun r s => (D.connection_regular j r s).differentiableAt (by norm_num))]
  have hm : matrixPartial (heatNormalFrameConnection g c D.point j) i 0 =
      (1 / 2 : ℝ) • curvatureEndomorphism (frameCurvature g c f) i j := by
    ext r s
    exact D.frame_connection_half_curvature i j r s
  rw [hm]
  change heatConnectionMatrixLinear ((1 / 2 : ℝ) • _) k l = _
  rw [map_smul]
  change (1 / 2 : ℝ) * heatTwoFormConnectionMatrix
    (curvatureEndomorphism (frameCurvature g c f) i j) k l = _
  have hR : (fun a b d h =>
      twoFormMetricCurvatureTensor g (⟨c, f⟩ : FrameBundle g) ![a,b,d,h]) =
      frameCurvature g c f := by
    funext a b d h
    simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
  rw [← hR, heatTwoFormConnectionMatrix_curvature]
  intro a b d h
  simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
  exact frame_algebraic_lastSkew f a b d h

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Uniform compact bounds for the actual transport family and the
coefficient left by the third transport equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise

noncomputable section

theorem HeatFamilySmoothCoefficients.lastCoefficient_regular (E : HeatFamilySmoothCoefficients)
    (k l : Fin 6) : ContDiff ℝ 2 (fun z => E.lastCoefficient z k l) :=
  heatFamilyBundleOperator_contDiff 2 E.a E.b E.B E.C _
    (fun i j => (E.a_regular i j).of_le (by norm_num))
    (fun i => (E.b_regular i).of_le (by norm_num))
    (fun i k l => (E.B_regular i k l).of_le (by norm_num))
    (fun k l => (E.C_regular k l).of_le (by norm_num))
    (fun q => E.amplitude_regular 3 (by omega) q l) k

theorem HeatFamilySmoothCoefficients.lastCoefficient_compact_bound (E : HeatFamilySmoothCoefficients)
    (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ z ∈ K, ∀ k l : Fin 6, |E.lastCoefficient z k l| ≤ C := by
  have hb (i : Fin 6 × Fin 6) : ∃ C ≥ (0 : ℝ), ∀ z ∈ K, |E.lastCoefficient z i.1 i.2| ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (E.lastCoefficient_regular i.1 i.2).continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro z hz
    have h : |E.lastCoefficient z i.1 i.2| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC z hz
    exact h.trans (le_max_left _ _)
  choose C hC hb using hb
  refine ⟨∑ i : Fin 6 × Fin 6, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro z hz k l
  exact (hb (k, l) z hz).trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ (k, l)))

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
theorem scalarBaseHeatWeight_half_sq (t : ℝ≥0) (i : ScalarBaseEigenIndex g o d) :
    scalarBaseHeatWeight g o d (t / 2) i ^ 2 = scalarBaseHeatWeight g o d t i := by
  simp only [scalarBaseHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constant scalar heat mode has multiplicity exactly one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_9
include o in
theorem smoothScalarBaseL2_one_ne_zero : smoothScalarBaseL2 g (smoothScalarConst 1) ≠ 0 := by
  intro h
  have hp := congrArg (scalarBasePullback g o) h
  rw [scalarBasePullback_smooth, map_zero] at hp
  have hf := smoothScalarValueL2_injective g o
    (hp.trans (map_zero (smoothScalarValueL2 g (canonicalFrameMeasure g o))).symm)
  have hv := congrArg (fun f : SmoothScalar (M := M) => f.val (Classical.arbitrary M)) hf
  change (1 : ℝ) = 0 at hv
  exact one_ne_zero hv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Four-component cutoff commutator for the actual one-form heat operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff _root_.Topology
noncomputable section

theorem fourHeatOneScaledCommutator_identity (a : FourSpace → Mat4)
    (b : FourSpace → Fin 4 → ℝ) (B : FourSpace → Fin 4 → Mat4)
    (χ : FourSpace → ℝ) (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (hu : ∀ m q, ContDiff ℝ 2 (fun y => u m y q)) (t : ℝ) (ht : 0 < t)
    (x : FourSpace) (k : Fin 4) :
    fourHeatLocalOperator (a x) (b x) 0 χ x *
        (fourHeatGaussian t x * fourHeatOnePolynomial u t x k) -
      2 * (∑ i, ∑ j, a x i j * partialDeriv χ i x *
        partialDeriv (fun y => fourHeatGaussian t y * fourHeatOnePolynomial u t y k) j x) +
      (∑ i, ∑ q, B x i k q * partialDeriv χ i x *
        (fourHeatGaussian t x * fourHeatOnePolynomial u t x q)) =
      (fourHeatGaussian t x / t) * fourHeatOneScaledCommutator a b B χ u t x k := by
  have hP (q : Fin 4) : DifferentiableAt ℝ (fun y => fourHeatOnePolynomial u t y q) x :=
    ((fourHeatPolynomial_contDiff (fun m y => u m y q) (fun m => hu m q) t).differentiable
      (by norm_num)).differentiableAt
  simp_rw [fourHeatGaussian_amplitude_partial_at t ht.ne' _ x (hP k)]
  unfold fourHeatOneScaledCommutator
  have hg : (∑ i, ∑ j, a x i j * partialDeriv χ i x *
      (fourHeatGaussian t x * (partialDeriv (fun y => fourHeatOnePolynomial u t y k) j x -
        x j / (2 * t) * fourHeatOnePolynomial u t x k))) =
      (fourHeatGaussian t x / t) * (∑ i, ∑ j, a x i j * partialDeriv χ i x *
        (t * partialDeriv (fun y => fourHeatOnePolynomial u t y k) j x -
          x j / 2 * fourHeatOnePolynomial u t x k)) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have hB : (∑ i, ∑ q, B x i k q * partialDeriv χ i x *
      (fourHeatGaussian t x * fourHeatOnePolynomial u t x q)) =
      fourHeatGaussian t x * (∑ i, ∑ q, B x i k q * partialDeriv χ i x *
        fourHeatOnePolynomial u t x q) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [hg, hB]
  field_simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single extended coefficient family provides the normal
bundle extension on every geometric slice where the germs agree. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

def HeatFamilySmoothCoefficients.normalExtension (E : HeatFamilySmoothCoefficients)
    {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 2 P (0, frameCoordinateState g c e))
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e))
    (ha : E.a =ᶠ[𝓝 (0, frameCoordinateState g c e)] (fun z => (heatFamilyMetric g c P z)⁻¹))
    (hb : E.b =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyDrift g c P)
    (hB : E.B =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyFirst g c P)
    (hC : E.C =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyZero g c P)
    (hU : E.U =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyLeading g c P) :
    HeatNormalBundleExtension D := by
  let q := frameCoordinateState g c e
  have hi : Tendsto (fun x : FourSpace => (x, q)) (𝓝 0) (𝓝 (0, q)) :=
    continuousAt_id.prodMk continuousAt_const
  have hG := heatFamilyNormal_germs D he P hP hpoint
  exact {
    base := {
      a := fun x => E.a (x, q)
      b := fun x => E.b (x, q)
      U := fun x => E.U (x, q)
      a_regular := fun i j => (E.a_regular i j).comp (contDiff_id.prodMk contDiff_const)
      b_regular := fun i => (E.b_regular i).comp (contDiff_id.prodMk contDiff_const)
      U_regular := E.U_regular.comp (contDiff_id.prodMk contDiff_const)
      U_pos := fun x => E.U_pos (x, q)
      a_near := Filter.EventuallyEq.trans (hi.eventually ha) hG.1
      b_near := Filter.EventuallyEq.trans (hi.eventually hb) hG.2.1
      U_near := Filter.EventuallyEq.trans (hi.eventually hU) hG.2.2.2.2 }
    B := fun x => E.B (x, q)
    C := fun x => E.C (x, q)
    B_regular := fun i k l => (E.B_regular i k l).comp (contDiff_id.prodMk contDiff_const)
    C_regular := fun k l => (E.C_regular k l).comp (contDiff_id.prodMk contDiff_const)
    B_near := Filter.EventuallyEq.trans (hi.eventually hB) hG.2.2.1
    C_near := Filter.EventuallyEq.trans (hi.eventually hC) hG.2.2.2.1 }

end
end PositiveEinsteinFour.Geometry
end


section

/-! Both terms of the cutoff heat residual vanish outside the spatial
support of the actual cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalCutoffParametrix_residual_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace)
    (hx : x ∉ tsupport χ) (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (k l : Fin 6) :
    deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
      fourHeatBundleOperator a b B C
        (fun y q => heatNormalCutoffParametrix E χ t y q l) x k = 0 := by
  have hχ : χ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
  have htime : (fun s => heatNormalCutoffParametrix E χ s x k l) = fun _ => (0 : ℝ) := by
    funext s
    simp only [heatNormalCutoffParametrix, hχ.self_of_nhds, zero_mul]
  have hspace (q : Fin 6) :
      (fun y => heatNormalCutoffParametrix E χ t y q l) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hχ] with y hy
    simp only [heatNormalCutoffParametrix, hy, zero_mul]
  rw [htime, deriv_const, fourHeatBundleOperator_zero_of_locally_zero a b B C hspace k,
    zero_add]

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
theorem smoothHarmonic_exact_eq_zero (hRic : RicciThree g) (u : smoothCovariantFields M 1)
    (hu : smoothOneFormExterior (o := o) u ∈ smoothHarmonicTwoForms) :
    smoothOneFormExterior (o := o) u = 0 :=
  smoothTwoFormL2Inner_definite _ (smoothHarmonic_orthogonal_exact hRic u _ hu)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth harmonic two-forms are preserved by Hodge star,
with finite positive and negative summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoFormDeRhamEnergy_hodge (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormDeRhamEnergy (smoothTwoFormHodge o u) = smoothTwoFormDeRhamEnergy u := by
  rw [smoothTwoForm_Weitzenbock hRic, smoothTwoForm_Weitzenbock hRic,
    smoothTwoFormCovariantEnergy_hodge, smoothTwoFormL2Inner_hodge_self]
  congr 2
  unfold smoothTwoFormL2Inner
  apply integral_congr_ae
  filter_upwards [] with x
  change inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g ⟨x,o.frame x⟩)
    (twoFormHodge (u.val x))) (twoFormHodge (u.val x)) =
      inner ℝ (twoFormCurvatureAction (twoFormMetricCurvatureTensor g ⟨x,o.frame x⟩)
        (u.val x)) (u.val x)
  rw [twoFormMetricCurvatureAction_hodge hRic]
  exact twoFormHodge.inner_map_map _ _

theorem smoothHarmonicTwoForms_hodge (hRic : RicciThree g) (u : smoothTwoForms o)
    (hu : u ∈ smoothHarmonicTwoForms) : smoothTwoFormHodge o u ∈ smoothHarmonicTwoForms := by
  apply (smoothTwoFormDeRhamEnergy_eq_zero_iff _).mp
  rw [smoothTwoFormDeRhamEnergy_hodge hRic]
  exact smoothHarmonicTwoForm_energy_zero u hu

def smoothHarmonicHodge (hRic : RicciThree g) :
    smoothHarmonicTwoForms (o := o) →ₗ[ℝ] smoothHarmonicTwoForms (o := o) where
  toFun u := ⟨smoothTwoFormHodge o u.val, smoothHarmonicTwoForms_hodge hRic u.val u.property⟩
  map_add' u v := Subtype.ext (map_add (smoothTwoFormHodge o) u.val v.val)
  map_smul' r u := Subtype.ext (map_smul (smoothTwoFormHodge o) r u.val)

theorem smoothHarmonicHodge_involutive (hRic : RicciThree g) :
    Function.Involutive (smoothHarmonicHodge (o := o) hRic) := by
  intro u
  apply Subtype.ext
  exact smoothTwoFormHodge_involutive o u.val

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms
def smoothHarmonicPositive (hRic : RicciThree g) :
    Submodule ℝ (smoothHarmonicTwoForms (o := o)) :=
  Module.End.eigenspace (R := ℝ) (M := smoothHarmonicTwoForms (o := o)) (smoothHarmonicHodge (o := o) hRic) (1 : ℝ)

def smoothHarmonicNegative (hRic : RicciThree g) :
    Submodule ℝ (smoothHarmonicTwoForms (o := o)) :=
  Module.End.eigenspace (R := ℝ) (M := smoothHarmonicTwoForms (o := o)) (smoothHarmonicHodge (o := o) hRic) (-1 : ℝ)

def smoothHarmonicPlus (hRic : RicciThree g) (u : smoothHarmonicTwoForms (o := o)) :
    smoothHarmonicPositive (o := o) hRic :=
  ⟨(2 : ℝ)⁻¹ • (u + smoothHarmonicHodge (o := o) hRic u), by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [map_smul, map_add, smoothHarmonicHodge_involutive, one_smul]
    rw [add_comm]⟩

def smoothHarmonicMinus (hRic : RicciThree g) (u : smoothHarmonicTwoForms (o := o)) :
    smoothHarmonicNegative (o := o) hRic :=
  ⟨(2 : ℝ)⁻¹ • (u - smoothHarmonicHodge (o := o) hRic u), by
    apply Module.End.mem_eigenspace_iff.mpr
    rw [map_smul, (smoothHarmonicHodge (o := o) hRic).map_sub,
      smoothHarmonicHodge_involutive, neg_one_smul]
    module⟩

theorem smoothHarmonic_decomposition (hRic : RicciThree g)
    (u : smoothHarmonicTwoForms (o := o)) :
    (smoothHarmonicPlus hRic u).val + (smoothHarmonicMinus hRic u).val = u := by
  change (2 : ℝ)⁻¹ • (u + smoothHarmonicHodge (o := o) hRic u) +
    (2 : ℝ)⁻¹ • (u - smoothHarmonicHodge (o := o) hRic u) = u
  module

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weak Hodge equation has an actual L2 forcing for the rough
resolvent. This is the equation used in local regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodgeEquation_rough_iff (u : TwoFormH1 o) (f : TwoFormL2 o) :
    (∀ v : TwoFormH1 o, twoFormHodgeForm u v = inner ℝ f (twoFormH1ToL2 v)) ↔
      u = twoFormRoughSolution (f + twoFormWeitzenbockPotential (twoFormH1ToL2 u)) := by
  constructor
  · intro hu
    apply twoFormRoughSolution_unique
    intro v
    have he := hu v
    unfold twoFormHodgeForm at he
    rw [inner_add_left]
    linarith only [he]
  · intro hu v
    have he := twoFormRoughSolution_weak
      (f + twoFormWeitzenbockPotential (twoFormH1ToL2 u)) v
    rw [← hu, inner_add_left] at he
    unfold twoFormHodgeForm
    linarith only [he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform compact bounds for the one-form transport amplitudes and residual. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

theorem HeatFamilyOneCoefficients.lastCoefficient_regular (E : HeatFamilyOneCoefficients)
    (k l : Fin 4) : ContDiff ℝ 2 (fun z => E.lastCoefficient z k l) :=
  heatFamilyOneOperator_contDiff 2 E.base.a E.base.b E.B E.C _
    (fun i j => (E.base.a_regular i j).of_le (by norm_num))
    (fun i => (E.base.b_regular i).of_le (by norm_num))
    (fun i k l => (E.B_regular i k l).of_le (by norm_num))
    (fun k l => (E.C_regular k l).of_le (by norm_num))
    (fun q => E.amplitude_regular 3 (by omega) q l) k

theorem HeatFamilyOneCoefficients.lastCoefficient_compact_bound (E : HeatFamilyOneCoefficients)
    (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ z ∈ K, ∀ k l : Fin 4, |E.lastCoefficient z k l| ≤ C := by
  have hb (i : Fin 4 × Fin 4) : ∃ C ≥ (0 : ℝ), ∀ z ∈ K, |E.lastCoefficient z i.1 i.2| ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
      (E.lastCoefficient_regular i.1 i.2).continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, ?_⟩
    intro z hz
    have h : |E.lastCoefficient z i.1 i.2| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC z hz
    exact h.trans (le_max_left _ _)
  choose C hC hb using hb
  refine ⟨∑ i : Fin 4 × Fin 4, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro z hz k l
  exact (hb (k, l) z hz).trans (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_univ (k, l)))


end
end PositiveEinsteinFour.Geometry
end


section

/-! A finite-smooth extension of the actual one-form coefficients, sharing
the scalar and two-form principal coefficients. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Filter
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem exists_heatFamilyOneCoefficients (E : HeatFamilySmoothCoefficients)
    (g : SmoothMetric M) (c : M) (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (z₀ : HeatRadialFrameSpace) (hP : ContDiffAt ℝ 12 P z₀)
    (hz : (P z₀).1 ∈ (chartAt FourSpace c).target)
    (hframe : (P z₀).2.det ≠ 0) (hmetric : 0 < (heatFamilyMetric g c P z₀).det) :
    ∃ F : HeatFamilyOneCoefficients, F.base = E ∧
      F.B =ᶠ[𝓝 z₀] heatFamilyOneFirst g c P ∧
      F.C =ᶠ[𝓝 z₀] heatFamilyOneZero g c P := by
  choose B hB hBc hBe using fun i k l => heatFamily_scalar_extension 10
    (fun z => heatFamilyOneFirst g c P z i k l) z₀
    (heatFamilyOneFirst_contDiffAt 10 g c P z₀ (hP.of_le (by norm_num)) hz hframe hmetric.ne' i k l)
  choose C hC hCc hCe using fun k l => heatFamily_scalar_extension 10
    (fun z => heatFamilyOneZero g c P z k l) z₀
    (heatFamilyOneZero_contDiffAt 10 g c P z₀ hP hz hframe hmetric k l)
  refine ⟨{
    base := E
    B := fun z i k l => B i k l z
    C := fun z k l => C k l z
    B_regular := hB
    C_regular := hC }, rfl, ?_, ?_⟩
  · filter_upwards [eventually_all.mpr (fun i => eventually_all.mpr
      (fun k => eventually_all.mpr (hBe i k)))] with z hz
    funext i k l
    exact hz i k l
  · filter_upwards [eventually_all.mpr (fun k => eventually_all.mpr (hCe k))] with z hz
    funext k l
    exact hz k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact bounds for scalar amplitudes and the remaining transport coefficient. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

theorem HeatFamilySmoothCoefficients.scalarLastCoefficient_regular (E : HeatFamilySmoothCoefficients) :
    ContDiff ℝ 2 E.scalarLastCoefficient :=
  heatFamilyScalarOperator_contDiff 2 E.a E.b _
    (fun i j => (E.a_regular i j).of_le (by norm_num))
    (fun i => (E.b_regular i).of_le (by norm_num)) (E.scalarAmplitude_regular 3 (by omega))

theorem HeatFamilySmoothCoefficients.scalarLastCoefficient_compact_bound
    (E : HeatFamilySmoothCoefficients) (K : Set HeatRadialFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ z ∈ K, |E.scalarLastCoefficient z| ≤ C := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn E.scalarLastCoefficient_regular.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  have h : |E.scalarLastCoefficient z| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC z hz
  exact h.trans (le_max_left _ _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! A common chart, coefficient extension and actual operator agreement
for every frame in one neighborhood. These are constructed geometric data. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem exists_heatUniformNormalFamily (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) :
    ∃ E : HeatFamilySmoothCoefficients, ∃ r > (0 : ℝ),
      ∃ U : Set (FrameBundle g), IsOpen U ∧ e ∈ U ∧
      (∀ e' ∈ U, frameCoordinateState g e.base e' ∈ ball (frameCoordinateState g e.base e) (r / 2) ∧
        Nonempty (HeatCommonNormalMember g o e.base E r e')) ∧
      ∃ C ≥ (0 : ℝ),
        (∀ m : ℕ, m ≤ 3 → ∀ n : ℕ, n ≤ 4 →
          ∀ z ∈ closedBall (0, frameCoordinateState g e.base e) r,
          ∀ k l : Fin 6, ‖iteratedFDeriv ℝ n (fun y => E.amplitude m y k l) z‖ ≤ C) ∧
        (∀ z ∈ closedBall (0, frameCoordinateState g e.base e) r,
          ∀ k l : Fin 6, |E.lastCoefficient z k l| ≤ C) := by
  obtain ⟨F, t, _, _, hP, U₀, hU₀, he₀, R, hR, hdata⟩ := exists_heatNormalCommonChart g o e
  let p := frameCoordinateState g e.base e
  let P := heatRadialFrameFamily F t
  obtain ⟨D₀, C₀, hD₀P, hC₀, hE₀, hCt₀, _, hRD₀⟩ := hdata e he₀
  have hzero : P (0, p) = p := by simpa only [hD₀P] using D₀.initial
  have hc : (P (0, p)).1 ∈ (chartAt FourSpace e.base).target := by
    simpa only [hD₀P] using D₀.in_chart 0 (mem_ball_self D₀.radius_pos)
  have hf : (P (0, p)).2.det ≠ 0 := by
    rw [hzero]
    have hg := congrArg Matrix.det (frameChartMatrix_normalizes g e.base e (mem_chart_source FourSpace e.base))
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hg
    change p.2.det * (metricInChart g e.base p.1).det * p.2.det = 1 at hg
    intro hz
    rw [hz] at hg
    norm_num at hg
  have hm : heatFamilyMetric g e.base P (0, p) = 1 := by
    have hh := D₀.metric_slice_eq P hD₀P 0 (mem_ball_self D₀.radius_pos)
      (hP.differentiableAt (by norm_num)) (by rw [frameExponential_zero]; exact mem_chart_source FourSpace e.base)
    exact hh.trans (heatNormalMetric_zero g o e)
  have hmp : 0 < (heatFamilyMetric g e.base P (0, p)).det := by rw [hm, Matrix.det_one]; norm_num
  obtain ⟨E, ha, hb, hB, hC, hU⟩ := exists_heatFamilySmoothCoefficients g e.base P (0, p) hP hc hf hmp
  have hdetc : ContinuousAt (fun z => (heatFamilyMetric g e.base P z).det) (0, p) :=
    (heatFamilyMatrixDeterminant_contDiffAt 0 _ (0, p)
      (heatFamilyMetric_contDiffAt 0 g e.base P (0, p) (hP.of_le (by norm_num)) hc)).continuousAt
  have hdetpos : ∀ᶠ z in 𝓝 ((0 : FourSpace), p), 0 < (heatFamilyMetric g e.base P z).det :=
    hdetc.preimage_mem_nhds (isOpen_Ioi.mem_nhds hmp)
  have hn : ∀ᶠ z in 𝓝 ((0 : FourSpace), p),
      ContDiffAt ℝ 2 P z ∧ 0 < (heatFamilyMetric g e.base P z).det ∧
      E.a =ᶠ[𝓝 z] (fun y => (heatFamilyMetric g e.base P y)⁻¹) ∧
      E.b =ᶠ[𝓝 z] heatFamilyDrift g e.base P ∧
      E.B =ᶠ[𝓝 z] heatFamilyFirst g e.base P ∧
      E.C =ᶠ[𝓝 z] heatFamilyZero g e.base P ∧
      E.U =ᶠ[𝓝 z] heatFamilyLeading g e.base P := by
    filter_upwards [(hP.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num),
      hdetpos, ha.eventuallyEq_nhds, hb.eventuallyEq_nhds, hB.eventuallyEq_nhds,
      hC.eventuallyEq_nhds, hU.eventuallyEq_nhds] with z hz hdz haz hbz hBz hCz hUz
    exact ⟨hz, hdz, haz, hbz, hBz, hCz, hUz⟩
  obtain ⟨S, hS, hball⟩ := Metric.mem_nhds_iff.mp hn
  let r := min R (S / 2)
  have hr : 0 < r := lt_min hR (half_pos hS)
  have hrR : r ≤ R := min_le_left _ _
  have hrS : r < S := (min_le_right _ _).trans_lt (half_lt_self hS)
  have hcoord : {e' : FrameBundle g | frameCoordinateState g e.base e' ∈ ball p (r / 2)} ∈ 𝓝 e :=
    (frameCoordinateState_continuousAt g e.base e (mem_chart_source FourSpace e.base)).preimage_mem_nhds
      (ball_mem_nhds _ (half_pos hr))
  obtain ⟨U, hsub, hUopen, heU⟩ := mem_nhds_iff.mp (Filter.inter_mem (hU₀.mem_nhds he₀) hcoord)
  have hpair (q : CoordinateFrameSpace) (hq : q ∈ ball p (r / 2))
      (x : FourSpace) (hx : x ∈ ball 0 r) : (x, q) ∈ ball (0, p) S := by
    change max (dist x 0) (dist q p) < S
    exact max_lt (lt_trans hx hrS) ((show dist q p < r / 2 from hq).trans
      ((half_lt_self hr).trans hrS))
  refine ⟨E, r, hr, U, hUopen, heU, ?_, ?_⟩
  · intro e' he'
    obtain ⟨he'₀, hq⟩ := hsub he'
    obtain ⟨D, C, hDP, hCs, hCE, hCt, hCi, hRD⟩ := hdata e' he'₀
    let q := frameCoordinateState g e.base e'
    obtain ⟨hPq, _, haq, hbq, hBq, hCq, hUq⟩ := hball (hpair q hq 0 (mem_ball_self hr))
    have he'c : e'.base ∈ (chartAt FourSpace e.base).source := by
      have hh := hCt (C.map_source (hCs ▸ mem_ball_self hR))
      rwa [hCE (hCs ▸ mem_ball_self hR), frameExponential_zero] at hh
    let A := E.normalExtension D he'c P hPq hDP haq hbq hBq hCq hUq
    have hbs : ball (0 : FourSpace) r ⊆ C.source := by rw [hCs]; exact ball_subset_ball hrR
    have hsource (x : FourSpace) (hx : x ∈ ball 0 r) :
        frameExponential g o e' x ∈ (chartAt FourSpace e.base).source := by
      rw [← hCE (hbs hx)]
      exact hCt (C.map_source (hbs hx))
    have hraw := heatFamilyNormal_on_ball D P hDP r (hrR.trans hRD)
      (fun x hx => (hball (hpair q hq x hx)).1) hsource
      (fun x hx => (hball (hpair q hq x hx)).2.1)
    refine ⟨hq, ⟨{
      frameData := D, extension := A, chart := C,
      radius_le := hrR.trans hRD,
      point_regular := ?_, metric_pos := ?_,
      ball_source := hbs, exponential := hCE, target_chart := hCt, inverse_regular := hCi,
      a_family := rfl, b_family := rfl, B_family := rfl, C_family := rfl, U_family := rfl,
      actual := ?_ }⟩⟩
    · intro x hx
      rw [hDP]
      exact ContDiffAt.comp (f := fun y : FourSpace => (y, q)) (g := P) x
        (hball (hpair q hq x hx)).1 (contDiffAt_id.prodMk contDiffAt_const)
    · intro x hx
      have hh := D.metric_slice_eq P hDP x (ball_subset_ball (hrR.trans hRD) hx)
        ((hball (hpair q hq x hx)).1.differentiableAt (by norm_num)) (hsource x hx)
      rw [← hh]
      exact (hball (hpair q hq x hx)).2.1
    · intro x hx
      obtain ⟨_, _, hax, hbx, hBx, hCx, hUx⟩ := hball (hpair q hq x hx)
      obtain ⟨ha', hb', hB', hC', hU'⟩ := hraw x hx
      exact ⟨hax.self_of_nhds.trans ha', hbx.self_of_nhds.trans hb',
        hBx.self_of_nhds.trans hB', hCx.self_of_nhds.trans hC', hUx.self_of_nhds.trans hU'⟩
  · obtain ⟨C₁, hC₁, hA⟩ := E.amplitude_compact_bound (closedBall (0, p) r) (isCompact_closedBall _ _)
    obtain ⟨C₂, hC₂, hL⟩ := E.lastCoefficient_compact_bound (closedBall (0, p) r) (isCompact_closedBall _ _)
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_, ?_⟩
    · intro m hm n hn z hz k l
      exact (hA m hm n hn z hz k l).trans (le_add_of_nonneg_right hC₂)
    · intro z hz k l
      exact (hL z hz k l).trans (le_add_of_nonneg_left hC₁)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual two-form L2 space is the Hilbert sum of the finite
eigenspaces of its compact shifted Hodge resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormSpectral_isHilbertSum (hRic : RicciThree g) :
    IsHilbertSum ℝ (fun μ : TwoFormSpectralValue (o := o) hRic => TwoFormSpectralSpace hRic μ)
      (fun μ => (TwoFormSpectralSpace hRic μ).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal (fun μ : TwoFormSpectralValue (o := o) hRic =>
    TwoFormSpectralSpace hRic μ)
    (twoFormShiftedResolvent_symmetric hRic).orthogonalFamily_eigenspaces'
  rw [twoFormSpectral_total hRic]

def twoFormSpectralEquiv (hRic : RicciThree g) :
    TwoFormL2 o ≃ₗᵢ[ℝ] lp (fun μ : TwoFormSpectralValue (o := o) hRic =>
      TwoFormSpectralSpace hRic μ) 2 :=
  (twoFormSpectral_isHilbertSum hRic).linearIsometryEquiv

theorem twoFormSpectral_sum (hRic : RicciThree g) (f : TwoFormL2 o) :
    HasSum (fun μ : TwoFormSpectralValue (o := o) hRic =>
      ((twoFormSpectralEquiv hRic f) μ : TwoFormL2 o)) f := by
  have h := (twoFormSpectral_isHilbertSum hRic).hasSum_linearIsometryEquiv_symm
    (twoFormSpectralEquiv hRic f)
  change HasSum (fun μ : TwoFormSpectralValue (o := o) hRic =>
    ((twoFormSpectralEquiv hRic f) μ : TwoFormL2 o))
    ((twoFormSpectralEquiv hRic).symm (twoFormSpectralEquiv hRic f)) at h
  rwa [LinearIsometryEquiv.symm_apply_apply] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The jointly extended one-form coefficients give actual normal extensions
with the prescribed common scalar principal part. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatFamilyOneCoefficients.normalExtension (F : HeatFamilyOneCoefficients)
    (D : HeatNormalFrameData g o c e) (base : HeatNormalExtension 10 g o e)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (P : HeatRadialFrameSpace → CoordinateFrameSpace)
    (hP : ContDiffAt ℝ 2 P (0, frameCoordinateState g c e))
    (hpoint : D.point = fun x => P (x, frameCoordinateState g c e))
    (hB : F.B =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyOneFirst g c P)
    (hC : F.C =ᶠ[𝓝 (0, frameCoordinateState g c e)] heatFamilyOneZero g c P) :
    HeatNormalOneExtension D := by
  let q := frameCoordinateState g c e
  have hi : Tendsto (fun x : FourSpace => (x, q)) (𝓝 0) (𝓝 (0, q)) :=
    continuousAt_id.prodMk continuousAt_const
  have hG := heatFamilyOneNormal_germs D he P hP hpoint
  exact {
    base := base
    B := fun x => F.B (x, q)
    C := fun x => F.C (x, q)
    B_regular := fun i k l => (F.B_regular i k l).comp (contDiff_id.prodMk contDiff_const)
    C_regular := fun k l => (F.C_regular k l).comp (contDiff_id.prodMk contDiff_const)
    B_near := Filter.EventuallyEq.trans (hi.eventually hB) hG.1
    C_near := Filter.EventuallyEq.trans (hi.eventually hC) hG.2 }

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar normal parametrix has the actual delta initial pairing
and may be differentiated under each compactly supported test integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {e : FrameBundle g}

theorem HeatNormalExtension.scalarCutoff_initial (E : HeatNormalExtension 10 g o e)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hc : HasCompactSupport χ) (hχ0 : χ 0 = 1) :
    Tendsto (fun t => ∫ x, E.scalarCutoff χ t x * f x) (𝓝[Ioi 0] 0) (𝓝 (f 0)) := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => (χ x * f x) * E.scalarAmplitude m x
  have hu (m : Fin 4) : Continuous (u m) :=
    hχf.mul (E.scalarAmplitude_regular m (by omega)).continuous
  have huc (m : Fin 4) : HasCompactSupport (u m) := hc.mul_right.mul_right
  have hb (m : Fin 4) : ∃ C : ℝ, ∀ x, ‖u m x‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((huc m).isCompact_range (hu m)).bddAbove_image continuous_norm.continuousOn
    exact ⟨C, fun x => hC (mem_image_of_mem _ (mem_range_self x))⟩
  choose C hC using hb
  have h := fourHeatPolynomial_approximate_identity u hu C hC
  have hz : u 0 0 = f 0 := by
    change (χ 0 * f 0) * E.scalarAmplitude 0 0 = f 0
    rw [hχ0, E.scalarAmplitude_zero, one_mul, mul_one]
  rw [hz] at h
  apply h.congr'
  exact Eventually.of_forall fun t => integral_congr_ae (Eventually.of_forall fun x => by
    dsimp only [HeatNormalExtension.scalarCutoff, HeatNormalExtension.scalarParametrix,
      fourHeatPolynomial, u]
    ring)

theorem HeatNormalExtension.scalarCutoff_pairing_deriv (E : HeatNormalExtension 10 g o e)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hc : HasCompactSupport χ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => ∫ x, E.scalarCutoff χ s x * f x)
      (∫ x, deriv (fun s => E.scalarCutoff χ s x) t * f x) t := by
  let u : Fin 4 → FourSpace → ℝ := fun m => E.scalarAmplitude m
  have h := fourHeat_compact_polynomial_pairing_deriv (fun x => χ x * f x) hχf hc.mul_right
    u (fun m => (E.scalarAmplitude_regular m (by omega)).continuous) t ht
  have hfun : (fun s => ∫ x, (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x)) =
      fun s => ∫ x, E.scalarCutoff χ s x * f x := by
    funext s
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x) =
        (χ x * (fourHeatGaussian s x * fourHeatPolynomial u s x)) * f x
      ring
  have hval : (∫ x, (χ x * f x) * fourHeatGaussianPolynomialTime u t x) =
      ∫ x, deriv (fun s => E.scalarCutoff χ s x) t * f x := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      have hd := (fourHeatGaussianPolynomial_hasDerivAt u t ht x).const_mul (χ x)
      change HasDerivAt (fun s => E.scalarCutoff χ s x)
        (χ x * fourHeatGaussianPolynomialTime u t x) t at hd
      change χ x * f x * fourHeatGaussianPolynomialTime u t x =
        deriv (fun s => E.scalarCutoff χ s x) t * f x
      rw [hd.deriv]
      ring
  rwa [hfun, hval] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded spectral multipliers on the actual two-form L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormSpectralMultiplier (hRic : RicciThree g)
    (a : TwoFormSpectralValue (o := o) hRic → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  (twoFormSpectralEquiv hRic).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lp.mapCLM 2
      (fun μ => a μ • ContinuousLinearMap.id ℝ (TwoFormSpectralSpace hRic μ))
      hC (fun μ => by
        calc
          ‖a μ • ContinuousLinearMap.id ℝ (TwoFormSpectralSpace hRic μ)‖ ≤ |a μ| := by
            apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
            intro v
            change ‖a μ • v‖ ≤ |a μ| * ‖v‖
            rw [norm_smul, Real.norm_eq_abs]
          _ ≤ C := ha μ)).comp
      (twoFormSpectralEquiv hRic).toContinuousLinearEquiv.toContinuousLinearMap)

theorem twoFormSpectralMultiplier_coordinate (hRic : RicciThree g)
    (a : TwoFormSpectralValue (o := o) hRic → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f : TwoFormL2 o) (μ : TwoFormSpectralValue hRic) :
    (twoFormSpectralEquiv hRic (twoFormSpectralMultiplier hRic a C hC ha f)) μ =
      a μ • (twoFormSpectralEquiv hRic f) μ := by
  change ((twoFormSpectralEquiv hRic)
    ((twoFormSpectralEquiv hRic).symm _)) μ = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem twoFormSpectralMultiplier_norm (hRic : RicciThree g)
    (a : TwoFormSpectralValue (o := o) hRic → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f : TwoFormL2 o) :
    ‖twoFormSpectralMultiplier hRic a C hC ha f‖ ≤ C * ‖f‖ := by
  rw [← (twoFormSpectralEquiv hRic).norm_map (twoFormSpectralMultiplier hRic a C hC ha f),
    ← (twoFormSpectralEquiv hRic).norm_map f]
  calc
    _ ≤ ‖C • twoFormSpectralEquiv hRic f‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro μ
      rw [twoFormSpectralMultiplier_coordinate, norm_smul, Real.norm_eq_abs]
      change |a μ| * ‖(twoFormSpectralEquiv hRic f) μ‖ ≤
        ‖C • (twoFormSpectralEquiv hRic f) μ‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha μ) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

theorem twoFormSpectralMultiplier_inner (hRic : RicciThree g)
    (a : TwoFormSpectralValue (o := o) hRic → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f h : TwoFormL2 o) :
    inner ℝ (twoFormSpectralMultiplier hRic a C hC ha f) h =
      ∑' μ, a μ * inner ℝ ((twoFormSpectralEquiv hRic f) μ)
        ((twoFormSpectralEquiv hRic h) μ) := by
  rw [← (twoFormSpectralEquiv hRic).inner_map_map, lp.inner_eq_tsum]
  apply tsum_congr
  intro μ
  rw [twoFormSpectralMultiplier_coordinate, real_inner_smul_left]

theorem twoFormSpectralMultiplier_selfAdjoint (hRic : RicciThree g)
    (a : TwoFormSpectralValue (o := o) hRic → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f h : TwoFormL2 o) :
    inner ℝ (twoFormSpectralMultiplier hRic a C hC ha f) h =
      inner ℝ f (twoFormSpectralMultiplier hRic a C hC ha h) := by
  calc
    _ = ∑' μ, a μ * inner ℝ ((twoFormSpectralEquiv hRic f) μ)
        ((twoFormSpectralEquiv hRic h) μ) := twoFormSpectralMultiplier_inner hRic a C hC ha f h
    _ = ∑' μ, a μ * inner ℝ ((twoFormSpectralEquiv hRic h) μ)
        ((twoFormSpectralEquiv hRic f) μ) := by
      apply tsum_congr
      intro μ
      rw [real_inner_comm]
    _ = inner ℝ (twoFormSpectralMultiplier hRic a C hC ha h) f :=
      (twoFormSpectralMultiplier_inner hRic a C hC ha h f).symm
    _ = _ := real_inner_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-coordinate Hodge operator agrees with the actual operator
on one geometric neighborhood for every smooth test section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalFrameData.rough_pullback_uniform_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    : ∀ᶠ x in 𝓝 (0 : FourSpace),
      ∀ (T : FourSpace → CovariantCoordinates 2),
      (∀ z ∈ (chartAt FourSpace c).target, ∀ a, ContDiffAt ℝ ∞ (fun y => T y a) z) →
      ∀ v : Fin 2 → Fin 4,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (T (D.point y).1)) i) j x v) +
        (∑ i, heatNormalDrift g o e x i *
          tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (T (D.point y).1)) i x v) =
        -frameTensor (D.point x).2
          (twoFormSecondTrace (metricInChart g c (D.point x).1)⁻¹
            (covariantDerivative g c (covariantDerivative g c T) (D.point x).1)) v := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hg : ∀ᶠ x in 𝓝 (0 : FourSpace),
      (D.point x).2ᵀ * metricInChart g c (D.point x).1 * (D.point x).2 = 1 := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    exact D.orthonormal x hx
  filter_upwards [hp, hg.eventually_nhds, D.inverseMetric_transport_near he,
    D.drift_transport_near he, ball_mem_nhds (0 : FourSpace) D.radius_pos]
      with x hpx hgx ha hb hx
  intro T hT v
  exact heatNormal_rough_pullback g c D.point T x hpx hT (D.in_chart x hx) hgx
    (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) ha hb v

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalFrameData.actual_tensor_rough_uniform_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    : ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ (u : M → TwoFormFour), TwoFormSmooth o u → ∀ hx : x ∈ ball 0 D.radius, ∀ v : Fin 2 → Fin 4,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x v) +
        (∑ i, heatNormalDrift g o e x i *
          tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x v) =
        -twoFormFramedRoughTrace o u (D.frame x hx) v := by
  filter_upwards [D.rough_pullback_uniform_near he] with x h
  intro u hu hx v
  rw [D.roughTrace_as_actual hu x hx]
  exact h (twoFormCoordinates o u c) (fun z hz => hu.coordinates_contDiffAt c z hz) v

theorem HeatNormalFrameData.actual_rough_components_uniform_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ (u : M → TwoFormFour), TwoFormSmooth o u → ∀ hx : x ∈ ball 0 D.radius, ∀ k : Fin 6,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
            (fun y l => heatNormalTwoFormValue o c D.point u y l) i) j x k) +
        (∑ i, heatNormalDrift g o e x i *
          fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
            (fun y l => heatNormalTwoFormValue o c D.point u y l) i x k) =
        -twoFormFrameValue o (twoFormRoughTraceField o u) (D.frame x hx) k := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hg : ∀ᶠ x in 𝓝 (0 : FourSpace),
      (D.point x).2ᵀ * metricInChart g c (D.point x).1 * (D.point x).2 = 1 := by
    filter_upwards [ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    exact D.orthonormal x hx
  filter_upwards [hp, hg.eventually_nhds, D.actual_tensor_rough_uniform_near he]
    with x hpx hgx hr
  intro u hu hx k
  let κ : CovariantCoordinates 2 →ₗ[ℝ] ℝ :=
    (PiLp.proj 2 (fun _ : Fin 6 => ℝ) k).toLinearMap.comp
      (twoFormExtractLinear.comp twoTensorMatrixLinear)
  have hκ (a : TwoFormFour) : κ (twoFormTensor a) = a k :=
    congrArg (fun b : TwoFormFour => b k) (heat_extract_twoFormTensor a)
  have hh : -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j •
      tensorCovariantDirection (heatNormalFrameConnection g c D.point)
        (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x) +
      (∑ i, heatNormalDrift g o e x i •
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x) =
      -twoFormFramedRoughTrace o u (D.frame x hx) := by
    funext v
    simpa only [Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      using hr u hu hx v
  have hh' := congrArg κ hh
  simp only [map_neg, map_add, map_sum, map_smul, smul_eq_mul] at hh'
  have hf (i : Fin 4) : κ (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
      (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x) =
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fun y l => heatNormalTwoFormValue o c D.point u y l) i x k := by
    rw [heatNormal_tensor_first hu c D.point x (hpx.of_le (by norm_num)) (D.in_chart x hx) hgx i, hκ]
    exact heatNormalTwoFormNabla_component hu c D.point x (hpx.of_le (by norm_num))
      (D.in_chart x hx) i k
  have hs (i j : Fin 4) : κ (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
      (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
        (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x) =
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fun y l => heatNormalTwoFormValue o c D.point u y l) i) j x k := by
    rw [heatNormal_tensor_second hu c D.point x hpx (D.in_chart x hx) hgx i j, hκ]
  have ht := hu.framedValue_roughTrace hRic (D.frame x hx)
  rw [twoFormFramedValue_eq] at ht
  rw [← ht, hκ] at hh'
  simpa only [hf, hs] using hh'

theorem HeatNormalFrameData.actual_bundle_operator_uniform_near {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ (u : smoothTwoForms o), ∀ _hx : x ∈ ball 0 D.radius, ∀ k : Fin 6,
      fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
        (fun y l => heatNormalTwoFormValue o c D.point u.val y l) x k =
      heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic u).val x k := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  filter_upwards [hp, D.actual_rough_components_uniform_near he hRic] with x hpx hr
  intro u hx k
  have hd : (D.point x).2.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det (D.orthonormal x hx)
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
    norm_num at hh
  have hA (i : Fin 4) (j l : Fin 6) : DifferentiableAt ℝ
      (fun y => heatTwoFormConnection g c D.point i y j l) x :=
    (heatTwoFormConnection_contDiffAt 1 c D.point x hpx (D.in_chart x hx) hd i j l).differentiableAt
      one_ne_zero
  have hv (l : Fin 6) : ContDiffAt ℝ 2
      (fun y => heatNormalTwoFormValue o c D.point u.val y l) x := by
    let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) l
    simpa only [Function.comp_def] using! π.contDiff.contDiffAt.comp x
      (heatNormalTwoFormValue_contDiffAt 2 u.property c D.point x hpx (D.in_chart x hx))
  rw [← heatNormalConnectionOperator_eq D _ x hA hv k]
  change (-(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
      fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
        (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fun y l => heatNormalTwoFormValue o c D.point u.val y l) i) j x k) +
    (∑ i, heatNormalDrift g o e x i * fourHeatCovariantDerivative
      (heatTwoFormConnection g c D.point)
      (fun y l => heatNormalTwoFormValue o c D.point u.val y l) i x k)) + _ = _
  rw [hr u.val u.property hx k, D.value_as_actual _ x hx, heat_smoothHodge_frameValue hRic u (D.frame x hx)]
  have hV := congrArg (fun a : TwoFormFour => a k) (D.potential_action_as_actual u.val x hx)
  change (∑ l, heatNormalPotential g c D.point x k l *
      heatNormalTwoFormValue o c D.point u.val x l) =
    6 * twoFormFrameValue o u.val (D.frame x hx) k -
      2 * twoFormFrameValue o (twoFormCurvatureField o u.val) (D.frame x hx) k at hV
  rw [hV]
  change -twoFormFrameValue o (twoFormRoughTraceField o u.val) (D.frame x hx) k +
      (6 * twoFormFrameValue o u.val (D.frame x hx) k -
        2 * twoFormFrameValue o (twoFormCurvatureField o u.val) (D.frame x hx) k) = _
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 heat semigroup for the nonnegative two-form Hodge
Laplacian, defined from its proved compact resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatRate (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) : ℝ :=
  μ.val⁻¹ - 1

theorem twoFormHeatRate_nonneg (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : 0 ≤ twoFormHeatRate hRic μ :=
  sub_nonneg.mpr ((one_le_inv₀ (twoFormSpectralValue_bounds hRic μ).1).mpr
    (twoFormSpectralValue_bounds hRic μ).2)

def twoFormHeatWeight (hRic : RicciThree g) (t : ℝ≥0)
    (μ : TwoFormSpectralValue (o := o) hRic) : ℝ :=
  Real.exp (-(t : ℝ) * twoFormHeatRate hRic μ)

theorem twoFormHeatWeight_bound (hRic : RicciThree g) (t : ℝ≥0)
    (μ : TwoFormSpectralValue (o := o) hRic) : |twoFormHeatWeight hRic t μ| ≤ 1 := by
  rw [twoFormHeatWeight, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg)
    (twoFormHeatRate_nonneg hRic μ)

def twoFormHeat (hRic : RicciThree g) (t : ℝ≥0) : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormSpectralMultiplier hRic (twoFormHeatWeight hRic t) 1 zero_le_one
    (twoFormHeatWeight_bound hRic t)

theorem twoFormHeat_coordinate (hRic : RicciThree g) (t : ℝ≥0) (f : TwoFormL2 o)
    (μ : TwoFormSpectralValue hRic) :
    (twoFormSpectralEquiv hRic (twoFormHeat hRic t f)) μ =
      twoFormHeatWeight hRic t μ • (twoFormSpectralEquiv hRic f) μ :=
  twoFormSpectralMultiplier_coordinate hRic _ _ _ _ f μ

theorem twoFormHeat_contraction (hRic : RicciThree g) (t : ℝ≥0) (f : TwoFormL2 o) :
    ‖twoFormHeat hRic t f‖ ≤ ‖f‖ := by
  simpa only [twoFormHeat, one_mul] using twoFormSpectralMultiplier_norm hRic
    (twoFormHeatWeight hRic t) 1 zero_le_one (twoFormHeatWeight_bound hRic t) f

theorem twoFormHeat_selfAdjoint (hRic : RicciThree g) (t : ℝ≥0) (f h : TwoFormL2 o) :
    inner ℝ (twoFormHeat hRic t f) h = inner ℝ f (twoFormHeat hRic t h) :=
  twoFormSpectralMultiplier_selfAdjoint hRic _ _ _ _ f h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of the actual shifted resolvent in its spectral
coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormSpectralValue_abs_le (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : |μ.val| ≤ 1 := by
  rw [abs_of_pos (twoFormSpectralValue_bounds hRic μ).1]
  exact (twoFormSpectralValue_bounds hRic μ).2

theorem twoFormShiftedResolvent_eq_multiplier (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedResolvent hRic f = twoFormSpectralMultiplier hRic
      (fun μ => μ.val) 1 zero_le_one (twoFormSpectralValue_abs_le hRic) f := by
  have hsum := (twoFormSpectral_sum hRic f).mapL (twoFormShiftedResolvent hRic)
  have hmult := twoFormSpectral_sum hRic (twoFormSpectralMultiplier hRic
    (fun μ => μ.val) 1 zero_le_one (twoFormSpectralValue_abs_le hRic) f)
  apply hsum.unique
  convert hmult using 1
  all_goals try with_reducible_and_instances rfl
  ext μ
  rw [twoFormSpectralMultiplier_coordinate]
  exact Module.End.mem_eigenspace_iff.mp ((twoFormSpectralEquiv hRic f) μ).property

theorem twoFormShiftedResolvent_coordinate (hRic : RicciThree g) (f : TwoFormL2 o)
    (μ : TwoFormSpectralValue hRic) :
    (twoFormSpectralEquiv hRic (twoFormShiftedResolvent hRic f)) μ =
      μ.val • (twoFormSpectralEquiv hRic f) μ := by
  rw [twoFormShiftedResolvent_eq_multiplier, twoFormSpectralMultiplier_coordinate]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Dominated convergence for contraction multipliers on the actual
two-form spectral decomposition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormSpectralMultiplier_sub_norm_sq (hRic : RicciThree g)
    (a b : TwoFormSpectralValue (o := o) hRic → ℝ)
    (ha : ∀ μ, |a μ| ≤ 1) (hb : ∀ μ, |b μ| ≤ 1) (f : TwoFormL2 o) :
    ‖twoFormSpectralMultiplier hRic a 1 zero_le_one ha f -
      twoFormSpectralMultiplier hRic b 1 zero_le_one hb f‖ ^ 2 =
      ∑' μ, (a μ - b μ) ^ 2 * ‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (twoFormSpectralEquiv hRic).inner_map_map,
    map_sub, lp.inner_eq_tsum]
  apply tsum_congr
  intro μ
  change inner ℝ
    ((twoFormSpectralEquiv hRic (twoFormSpectralMultiplier hRic a 1 zero_le_one ha f)) μ -
      (twoFormSpectralEquiv hRic (twoFormSpectralMultiplier hRic b 1 zero_le_one hb f)) μ)
    ((twoFormSpectralEquiv hRic (twoFormSpectralMultiplier hRic a 1 zero_le_one ha f)) μ -
      (twoFormSpectralEquiv hRic (twoFormSpectralMultiplier hRic b 1 zero_le_one hb f)) μ) = _
  rw [twoFormSpectralMultiplier_coordinate, twoFormSpectralMultiplier_coordinate,
    ← sub_smul, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem twoFormSpectralMultiplier_tendsto {α : Type*} {l : Filter α}
    (hRic : RicciThree g) (a : α → TwoFormSpectralValue (o := o) hRic → ℝ)
    (b : TwoFormSpectralValue (o := o) hRic → ℝ)
    (ha : ∀ x μ, |a x μ| ≤ 1) (hb : ∀ μ, |b μ| ≤ 1)
    (hab : ∀ μ, Tendsto (fun x => a x μ) l (𝓝 (b μ))) (f : TwoFormL2 o) :
    Tendsto (fun x => twoFormSpectralMultiplier hRic (a x) 1 zero_le_one (ha x) f) l
      (𝓝 (twoFormSpectralMultiplier hRic b 1 zero_le_one hb f)) := by
  have hsum : Summable (fun μ : TwoFormSpectralValue (o := o) hRic =>
      4 * ‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2) := by
    have hs := lp.summable_inner (𝕜 := ℝ)
      (twoFormSpectralEquiv hRic f) (twoFormSpectralEquiv hRic f)
    simp only [real_inner_self_eq_norm_sq] at hs
    exact hs.mul_left 4
  have hbound (x : α) (μ : TwoFormSpectralValue (o := o) hRic) :
      ‖(a x μ - b μ) ^ 2 * ‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2‖ ≤
        4 * ‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2 := by
    have hdiff : |a x μ - b μ| ≤ 2 :=
      (abs_sub (a x μ) (b μ)).trans (by linarith only [ha x μ, hb μ])
    have hsq : (a x μ - b μ) ^ 2 ≤ 4 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hdiff)
        (add_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (abs_nonneg (a x μ - b μ)))
      nlinarith only [hprod, sq_abs (a x μ - b μ)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hpoint (μ : TwoFormSpectralValue (o := o) hRic) :
      Tendsto (fun x => (a x μ - b μ) ^ 2 * ‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2)
        l (𝓝 (0 : ℝ)) := by
    convert (((hab μ).sub_const (b μ)).pow 2).mul_const
      (‖(twoFormSpectralEquiv hRic f) μ‖ ^ 2) using 1
    all_goals try with_reducible_and_instances rfl
    simp
  have ht := tendsto_tsum_of_dominated_convergence hsum hpoint
    (Eventually.of_forall hbound)
  simp only [tsum_zero] at ht
  have hn : Tendsto (fun x => ‖twoFormSpectralMultiplier hRic (a x) 1 zero_le_one (ha x) f -
      twoFormSpectralMultiplier hRic b 1 zero_le_one hb f‖ ^ 2) l (𝓝 (0 : ℝ)) := by
    simpa only [twoFormSpectralMultiplier_sub_norm_sq] using ht
  have hs := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hs using 1
  · funext x
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  · exact congrArg nhds Real.sqrt_zero.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strong continuity of the actual two-form heat semigroup. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped Manifold ContDiff _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatWeight_continuous (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    Continuous (fun t : ℝ≥0 => twoFormHeatWeight hRic t μ) := by
  change Continuous (fun t : ℝ≥0 => Real.exp (-(t : ℝ) * twoFormHeatRate hRic μ))
  exact Real.continuous_exp.comp (continuous_subtype_val.neg.mul_const _)

theorem twoFormHeat_continuous (hRic : RicciThree g) (f : TwoFormL2 o) :
    Continuous (fun t : ℝ≥0 => twoFormHeat hRic t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact twoFormSpectralMultiplier_tendsto hRic (twoFormHeatWeight hRic)
    (twoFormHeatWeight hRic t) (twoFormHeatWeight_bound hRic)
    (twoFormHeatWeight_bound hRic t)
    (fun μ => (twoFormHeatWeight_continuous hRic μ).continuousAt) f

theorem twoFormHeat_joint_continuous (hRic : RicciThree g) :
    Continuous (fun tf : ℝ≥0 × TwoFormL2 o => twoFormHeat hRic tf.1 tf.2) := by
  apply continuous_iff_continuousAt.mpr
  intro tf
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have htime := Metric.continuousAt_iff.mp
    ((twoFormHeat_continuous hRic tf.2).continuousAt (x := tf.1))
    (ε / 2) (half_pos hε)
  obtain ⟨δ, hδ, htime⟩ := htime
  refine ⟨min δ (ε / 2), lt_min hδ (half_pos hε), ?_⟩
  intro sf hsf
  have hst : dist sf.1 tf.1 < δ := by
    calc
      dist sf.1 tf.1 ≤ dist sf tf := by rw [Prod.dist_eq]; exact le_max_left _ _
      _ < δ := lt_of_lt_of_le hsf (min_le_left _ _)
  have hsu : dist sf.2 tf.2 < ε / 2 := by
    calc
      dist sf.2 tf.2 ≤ dist sf tf := by rw [Prod.dist_eq]; exact le_max_right _ _
      _ < ε / 2 := lt_of_lt_of_le hsf (min_le_right _ _)
  calc
    dist (twoFormHeat hRic sf.1 sf.2) (twoFormHeat hRic tf.1 tf.2) ≤
        dist (twoFormHeat hRic sf.1 sf.2) (twoFormHeat hRic sf.1 tf.2) +
        dist (twoFormHeat hRic sf.1 tf.2) (twoFormHeat hRic tf.1 tf.2) := dist_triangle _ _ _
    _ ≤ dist sf.2 tf.2 + dist (twoFormHeat hRic sf.1 tf.2) (twoFormHeat hRic tf.1 tf.2) := by
      apply add_le_add_left
      rw [dist_eq_norm, ← map_sub, dist_eq_norm]
      exact twoFormHeat_contraction hRic sf.1 (sf.2 - tf.2)
    _ < ε / 2 + ε / 2 := add_lt_add hsu (htime hst)
    _ = ε := add_halves ε

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time heat lies in the actual weak Hodge domain. The
resolvent lift is obtained from an explicit bounded spectral multiplier. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatLiftWeight_bound (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    |μ.val⁻¹ * twoFormHeatWeight hRic t μ| ≤ Real.exp t / t := by
  have htR : 0 < (t : ℝ) := ht
  have hm := (twoFormSpectralValue_bounds hRic μ).1
  have he : (t : ℝ) * μ.val⁻¹ ≤ Real.exp ((t : ℝ) * μ.val⁻¹) := by
    have h := Real.add_one_le_exp ((t : ℝ) * μ.val⁻¹)
    linarith only [h]
  have he' := mul_le_mul_of_nonneg_right he
    (Real.exp_pos (-((t : ℝ) * μ.val⁻¹))).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at he'
  have hweight : twoFormHeatWeight hRic t μ =
      Real.exp t * Real.exp (-((t : ℝ) * μ.val⁻¹)) := by
    rw [twoFormHeatWeight, twoFormHeatRate, ← Real.exp_add]
    congr 1
    ring
  rw [hweight, abs_of_pos (mul_pos (inv_pos.mpr hm)
    (mul_pos (Real.exp_pos _) (Real.exp_pos _)))]
  calc
    μ.val⁻¹ * (Real.exp t * Real.exp (-((t : ℝ) * μ.val⁻¹))) =
        (Real.exp t / t) * (((t : ℝ) * μ.val⁻¹) * Real.exp (-((t : ℝ) * μ.val⁻¹))) := by
      field_simp [ne_of_gt htR]
    _ ≤ (Real.exp t / t) * 1 := mul_le_mul_of_nonneg_left he' (by positivity)
    _ = _ := mul_one _

def twoFormHeatLiftSource (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormSpectralMultiplier hRic (fun μ => μ.val⁻¹ * twoFormHeatWeight hRic t μ)
    (Real.exp t / t) (by positivity) (twoFormHeatLiftWeight_bound hRic t ht)

theorem twoFormHeatLiftSource_resolvent (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) :
    twoFormShiftedResolvent hRic (twoFormHeatLiftSource hRic t ht f) = twoFormHeat hRic t f := by
  apply (twoFormSpectralEquiv hRic).injective
  apply lp.ext
  funext μ
  rw [twoFormShiftedResolvent_coordinate, twoFormHeat_coordinate]
  change μ.val • (twoFormSpectralEquiv hRic
    (twoFormSpectralMultiplier hRic _ _ _ _ f)) μ = _
  rw [twoFormSpectralMultiplier_coordinate, smul_smul]
  congr 1
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (twoFormSpectralValue_bounds hRic μ).1), one_mul]

def twoFormHeatLift (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) :
    TwoFormL2 o →L[ℝ] TwoFormH1 o :=
  (twoFormShiftedSolution hRic).comp (twoFormHeatLiftSource hRic t ht)

theorem twoFormHeatLift_value (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (f : TwoFormL2 o) : twoFormH1ToL2 (twoFormHeatLift hRic t ht f) = twoFormHeat hRic t f :=
  twoFormHeatLiftSource_resolvent hRic t ht f

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every compact chart coefficient of an actual smooth two-form lies
in every integer Sobolev space. This supplies smooth Hodge-Poisson data. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_smooth_gram_integer (n : ℕ) (c : M) (S : Mat4) {K : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ K) (v : Fin 2 → Fin 4) (w : smoothTwoForms o) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt η hη hcη hsη v (smoothTwoFormToH1 (w : SmoothH1TwoForm o))) :
        𝓢'(FourSpace, ℂ)) := by
  let A : FourSpace → ℝ := fun z => η z * frameTensor (chartGramMatrix g c S z)
    (twoFormCoordinates o w.val c z) v
  have hA : ContDiff ℝ ∞ A := by
    apply scalarCutoff_contDiff η _ hη
    intro z hz
    exact contDiffAt_pi.mp (w.property.gramTensor_contDiffAt c S z (hKt (hsη hz))) v
  have hcA : HasCompactSupport A := hcη.mul_right
  let ψ := (hcA.toSchwartzMap hA).postcompCLM Complex.ofRealCLM
  have he : scalarComplexL2 (twoFormGramValueL2 c S hK hKt η hη hcη hsη v
      (smoothTwoFormToH1 (w : SmoothH1TwoForm o))) = ψ.toLp 2 volume := by
    apply Lp.ext
    filter_upwards [scalarComplexL2_coe (twoFormGramValueL2 c S hK hKt η hη hcη hsη v
      (smoothTwoFormToH1 (w : SmoothH1TwoForm o))),
      twoFormGramValueL2_coe c S hK hKt η hη hcη hsη v (w : SmoothH1TwoForm o),
      ψ.coeFn_toLp 2 volume] with z hc hg hψ
    rw [hc, hg, hψ]
    rfl
  rw [he, Lp.toTemperedDistribution_toLp_eq]
  exact ψ.memSobolev

theorem twoForm_smooth_source_integer (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    (hsη : tsupport η ⊆ K) (w : smoothTwoForms o) (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη hsη hS
        (smoothTwoFormToL2 (w : SmoothL2TwoForm o)))) : 𝓢'(FourSpace, ℂ)) := by
  have he := twoFormL2GramValue_H1 c S hS hK hKt η hη hcη hsη
    (smoothTwoFormToH1 (w : SmoothH1TwoForm o))
  have hJ := twoFormH1ToL2_smooth (w : SmoothH1TwoForm o)
  have htarget : twoFormL2GramValue c S hK hKt η hη hcη hsη hS
      (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) =
      twoFormGramVectorL2 c S hK hKt η hη hcη hsη (smoothTwoFormToH1 (w : SmoothH1TwoForm o)) :=
    (congrArg (twoFormL2GramValue c S hK hKt η hη hcη hsη hS) hJ).symm.trans he
  rw [htarget, twoFormGramVectorComponent]
  exact twoForm_smooth_gram_integer n c S hK hKt η hη hcη hsη (twoFormComponentIndex r) w

end
end PositiveEinsteinFour.Geometry
end


section

/-! At positive time the actual heat operator is in the range of every
power of the compact Hodge resolvent, with explicit multiplier bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatPowerWeight_bound (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (n : ℕ) (μ : TwoFormSpectralValue (o := o) hRic) :
    |μ.val⁻¹ ^ n * twoFormHeatWeight hRic t μ| ≤
      Real.exp t * (n.factorial : ℝ) / (t : ℝ) ^ n := by
  have htR : 0 < (t : ℝ) := ht
  have hm := (twoFormSpectralValue_bounds hRic μ).1
  have hy : 0 ≤ (t : ℝ) * μ.val⁻¹ := mul_nonneg htR.le (inv_pos.mpr hm).le
  have hn : 0 < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have he := (div_le_iff₀ hn).mp
    (Real.pow_div_factorial_le_exp ((t : ℝ) * μ.val⁻¹) hy n)
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-((t : ℝ) * μ.val⁻¹))).le
  have heq : (Real.exp ((t : ℝ) * μ.val⁻¹) * (n.factorial : ℝ)) *
      Real.exp (-((t : ℝ) * μ.val⁻¹)) = (n.factorial : ℝ) := by
    rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  rw [heq] at he'
  have hw : twoFormHeatWeight hRic t μ =
      Real.exp t * Real.exp (-((t : ℝ) * μ.val⁻¹)) := by
    rw [twoFormHeatWeight, twoFormHeatRate, ← Real.exp_add]
    congr 1
    ring
  rw [hw, abs_of_pos (mul_pos (pow_pos (inv_pos.mpr hm) n)
    (mul_pos (Real.exp_pos _) (Real.exp_pos _)))]
  calc
    _ = (Real.exp t / (t : ℝ) ^ n) *
        (((t : ℝ) * μ.val⁻¹) ^ n * Real.exp (-((t : ℝ) * μ.val⁻¹))) := by
      rw [mul_pow]
      field_simp [ne_of_gt htR]
    _ ≤ (Real.exp t / (t : ℝ) ^ n) * (n.factorial : ℝ) :=
      mul_le_mul_of_nonneg_left he' (by positivity)
    _ = _ := by ring

def twoFormHeatPowerSource (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormSpectralMultiplier hRic (fun μ => μ.val⁻¹ ^ n * twoFormHeatWeight hRic t μ)
    (Real.exp t * (n.factorial : ℝ) / (t : ℝ) ^ n) (by positivity)
    (twoFormHeatPowerWeight_bound hRic t ht n)

theorem twoFormResolvent_power_coordinate (hRic : RicciThree g) (n : ℕ) (f : TwoFormL2 o)
    (μ : TwoFormSpectralValue hRic) :
    (twoFormSpectralEquiv hRic ((twoFormShiftedResolvent hRic ^ n) f)) μ =
      μ.val ^ n • (twoFormSpectralEquiv hRic f) μ := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      change (twoFormSpectralEquiv hRic
        ((twoFormShiftedResolvent hRic ^ n) (twoFormShiftedResolvent hRic f))) μ = _
      rw [ih, twoFormShiftedResolvent_coordinate, smul_smul, ← pow_succ]

theorem twoFormHeatPowerSource_resolvent (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
    (n : ℕ) (f : TwoFormL2 o) :
    (twoFormShiftedResolvent hRic ^ n) (twoFormHeatPowerSource hRic t ht n f) =
      twoFormHeat hRic t f := by
  apply (twoFormSpectralEquiv hRic).injective
  apply lp.ext
  funext μ
  rw [twoFormResolvent_power_coordinate, twoFormHeat_coordinate]
  change μ.val ^ n • (twoFormSpectralEquiv hRic
    (twoFormSpectralMultiplier hRic _ _ _ _ f)) μ = _
  rw [twoFormSpectralMultiplier_coordinate, smul_smul]
  congr 1
  rw [← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ (ne_of_gt (twoFormSpectralValue_bounds hRic μ).1), one_pow, one_mul]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory09
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The lower-order harmonic source has one fewer derivative than the
locally controlled two-form, at every finite order used by the bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V) (b : TwoFormFour)

include hV hreg in
theorem twoFormHarmonicDivergenceSource_integer :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
        (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
          (twoFormWeitzenbockPotential (twoFormH1ToL2 u)))
        (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
      𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (_ - _))
  rw [map_sub]
  apply MemSobolev.sub
  · apply twoFormCoefficientPair_memSobolev_integer
      (twoFormMassCoefficient (g := g) c η b)
      (twoFormMassCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b)
      hcη.mul_right.smul_right n
    intro r
    rw [map_sub]
    change MemSobolev (n : ℝ) 2 (C (_ - _))
    rw [map_sub]
    have hp := (twoFormPotential_local_integer (n + 1) c S hS hK hKt hV hVK u hreg
      η hη hcη hηV r).mono hle
    have hv : MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)) : 𝓢'(FourSpace, ℂ)) := by
      rw [twoFormGramVectorComponent]
      exact (hreg η hη hcη hηV (twoFormComponentIndex r)).mono hle
    exact hp.sub hv
  · apply scalarReal_memSobolev_finset n
    intro i _
    exact twoFormCoefficientPair_memSobolev_integer
      (fun z => η z • twoFormWeightedConnection (g := g) c S b i z)
      (twoFormCutoffWeightedConnection_smooth c S hS b i η hη ((hηV.trans hVK).trans hKt))
      hcη.smul_right n _
      (twoFormInnerNabla_component_integer n c S hS hK hKt hVK u hreg η hη hcη hηV i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth forcing in the actual Hodge-Poisson equation has the finite
Sobolev regularity required by the local elliptic bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o) (w : smoothTwoForms o)
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hreg in
theorem twoFormPoisson_forcing_integer (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
          smoothTwoFormToL2 (w : SmoothL2TwoForm o)))) : 𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (twoFormVectorComponentL2 r
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + smoothTwoFormToL2 (w : SmoothL2TwoForm o)))))
  simp only [map_add]
  exact ((twoFormPotential_local_integer (n + 1) c S hS hK hKt hV hVK u hreg
    η hη hcη hηV r).mono hle).add
      (twoForm_smooth_source_integer n c S hS hK hKt η hη hcη (hηV.trans hVK) w r)

include hV hreg in
theorem twoFormPoissonDivergenceSource_integer (b : TwoFormFour) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
        (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
          (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
            smoothTwoFormToL2 (w : SmoothL2TwoForm o)))
        (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
      𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (_ - _))
  rw [map_sub]
  apply MemSobolev.sub
  · apply twoFormCoefficientPair_memSobolev_integer
      (twoFormMassCoefficient (g := g) c η b)
      (twoFormMassCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b)
      hcη.mul_right.smul_right n
    intro r
    rw [map_sub]
    change MemSobolev (n : ℝ) 2 (C (_ - _))
    rw [map_sub]
    have hv : MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)) : 𝓢'(FourSpace, ℂ)) := by
      rw [twoFormGramVectorComponent]
      exact (hreg η hη hcη hηV (twoFormComponentIndex r)).mono hle
    exact (twoFormPoisson_forcing_integer n c S hS hK hKt hV hVK u w hreg η hη hcη hηV r).sub hv
  · apply scalarReal_memSobolev_finset n
    intro i _
    exact twoFormCoefficientPair_memSobolev_integer
      (fun z => η z • twoFormWeightedConnection (g := g) c S b i z)
      (twoFormCutoffWeightedConnection_smooth c S hS b i η hη ((hηV.trans hVK).trans hKt))
      hcη.smul_right n _
      (twoFormInnerNabla_component_integer n c S hS hK hKt hVK u hreg η hη hcη hηV i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite-regularity source in the actual Hodge equation has the finite
Sobolev regularity required by the local elliptic bootstrap. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (n : ℕ) (c : M) (S : Mat4) (hS : Sᵀ * S = 1) {K V : Set FourSpace}
  (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (u : TwoFormH1 o) (f : TwoFormL2 o)

  (hsource : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (r : Fin 6), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormVectorComponentL2 r (twoFormL2GramValue c S hK hKt a ha hc
        (hs.trans hVK) hS f)) : 𝓢'(FourSpace, ℂ)))
  (hreg : ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev ((n + 1 : ℕ) : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ)))
  (η : FourSpace → ℝ) (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
  (hηV : tsupport η ⊆ V)

include hV hsource hreg in
theorem twoFormRegularSource_forcing_integer (r : Fin 6) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
      (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
        (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
          f))) : 𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (twoFormVectorComponentL2 r
    (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
      (twoFormWeitzenbockPotential (twoFormH1ToL2 u) + f))))
  simp only [map_add]
  exact ((twoFormPotential_local_integer (n + 1) c S hS hK hKt hV hVK u hreg
    η hη hcη hηV r).mono hle).add
      (hsource η hη hcη hηV r)

include hV hsource hreg in
theorem twoFormRegularSourceDivergenceSource_integer (b : TwoFormFour) :
    MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormDivergenceSource (g := g) c S hS η hη hcη ((hηV.trans hVK).trans hKt) b
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)
        (twoFormL2GramValue c S hK hKt η hη hcη (hηV.trans hVK) hS
          (twoFormWeitzenbockPotential (twoFormH1ToL2 u) +
            f))
        (fun i => twoFormGramNablaL2 c S hS hK hKt η hη hcη (hηV.trans hVK) i u)) :
      𝓢'(FourSpace, ℂ)) := by
  let C : Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] 𝓢'(FourSpace, ℂ) :=
    ((Lp.toTemperedDistributionCLM ℂ volume 2).restrictScalars ℝ).comp
      (Complex.ofRealCLM.compLpL 2 volume)
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
  change MemSobolev (n : ℝ) 2 (C (_ - _))
  rw [map_sub]
  apply MemSobolev.sub
  · apply twoFormCoefficientPair_memSobolev_integer
      (twoFormMassCoefficient (g := g) c η b)
      (twoFormMassCoefficient_smooth (g := g) c η hη ((hηV.trans hVK).trans hKt) b)
      hcη.mul_right.smul_right n
    intro r
    rw [map_sub]
    change MemSobolev (n : ℝ) 2 (C (_ - _))
    rw [map_sub]
    have hv : MemSobolev (n : ℝ) 2 (scalarComplexL2 (twoFormVectorComponentL2 r
        (twoFormGramVectorL2 c S hK hKt η hη hcη (hηV.trans hVK) u)) : 𝓢'(FourSpace, ℂ)) := by
      rw [twoFormGramVectorComponent]
      exact (hreg η hη hcη hηV (twoFormComponentIndex r)).mono hle
    exact (twoFormRegularSource_forcing_integer n c S hS hK hKt hV hVK u f hsource hreg η hη hcη hηV r).sub hv
  · apply scalarReal_memSobolev_finset n
    intro i _
    exact twoFormCoefficientPair_memSobolev_integer
      (fun z => η z • twoFormWeightedConnection (g := g) c S b i z)
      (twoFormCutoffWeightedConnection_smooth c S hS b i η hη ((hηV.trans hVK).trans hKt))
      hcη.smul_right n _
      (twoFormInnerNabla_component_integer n c S hS hK hKt hVK u hreg η hη hcη hηV i)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite-order local regularity of the actual shifted Hodge resolvent.
The forcing is an H1 section with the indicated local Sobolev order. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def TwoFormChartSobolev (n : ℕ) (c : M) (S : Mat4) {K V : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hVK : V ⊆ K) (u : TwoFormH1 o) : Prop :=
  ∀ (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ V) (v : Fin 2 → Fin 4), MemSobolev (n : ℝ) 2 (scalarComplexL2
      (twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) v u) : 𝓢'(FourSpace, ℂ))

theorem TwoFormChartSobolev.mono {n m : ℕ} {c : M} {S : Mat4} {K V : Set FourSpace}
    {hK : IsCompact K} {hKt : K ⊆ (chartAt FourSpace c).target} {hVK : V ⊆ K}
    {u : TwoFormH1 o} (h : TwoFormChartSobolev m c S hK hKt hVK u) (hnm : n ≤ m) :
    TwoFormChartSobolev n c S hK hKt hVK u := by
  intro a ha hc hs v
  exact (h a ha hc hs v).mono (by exact_mod_cast hnm)

theorem twoFormChartSobolev_one (c : M) (S : Mat4) {K V : Set FourSpace}
    (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (hVK : V ⊆ K) (u : TwoFormH1 o) : TwoFormChartSobolev 1 c S hK hKt hVK u := by
  intro a ha hc hs v
  simpa only [Nat.cast_one] using
    twoFormGram_memSobolev_one c S hK hKt a ha hc (hs.trans hVK) v u

theorem twoFormShiftedSolution_rough (hRic : RicciThree g) (f : TwoFormL2 o) :
    twoFormShiftedSolution hRic f = twoFormRoughSolution
      (twoFormWeitzenbockPotential (twoFormH1ToL2 (twoFormShiftedSolution hRic f)) +
        (f - twoFormH1ToL2 (twoFormShiftedSolution hRic f))) := by
  apply twoFormRoughSolution_unique
  intro v
  have he := twoFormShiftedSolution_weak hRic f v
  unfold twoFormHodgeForm at he
  rw [inner_add_left, inner_sub_left]
  linarith only [he]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local heat coefficients are bounded continuous functions, with a bound
by the L2 norm of the initial section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Matrix TemperedDistribution
open scoped BigOperators Manifold ContDiff SchwartzMap NNReal BoundedContinuousFunction

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (t : ℝ≥0) (ht : 0 < t)
  (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
  {K V : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (hV : IsOpen V) (hVK : V ⊆ K) (U : Set FourSpace) (hU : IsOpen U)
  (hUt : U ⊆ (chartAt FourSpace c).target) (hKU : K ⊆ U)
  (hp : ∀ z (hz : z ∈ U), chartGramSection g c S hS ⟨z, hUt hz⟩ ∈ o.positive)
  (a : FourSpace → ℝ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a)
  (hs : tsupport a ⊆ V) (r : Fin 6)

def twoFormHeatChartL2 : TwoFormL2 o →L[ℝ] Lp ℂ 2 (volume : Measure FourSpace) :=
  (Complex.ofRealCLM.compLpL 2 volume).comp
    ((twoFormGramValueL2 c S hK hKt a ha hc (hs.trans hVK) (twoFormComponentIndex r)).comp
      (twoFormHeatLift hRic t ht))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The shifted Hodge resolvent commutes with the actual Hodge
involution. Consequently each finite spectral space is graded. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodgeForm_hodge_left (hRic : RicciThree g) (u v : TwoFormH1 o) :
    twoFormHodgeForm (twoFormH1Hodge u) v = twoFormHodgeForm u (twoFormH1Hodge v) := by
  unfold twoFormHodgeForm
  rw [twoFormH1Hodge_selfAdjoint, twoFormH1ToL2_hodge,
    twoFormWeitzenbockPotential_hodge hRic, twoFormL2Hodge_selfAdjoint, twoFormH1ToL2_hodge]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Hodge operator as a densely defined operator on L2.
Its domain is the range of the shifted resolvent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodgeDomain_weak (hRic : RicciThree g)
    (f : twoFormHodgeDomain (o := o) hRic) :
    ∃ u : TwoFormH1 o, twoFormH1ToL2 u = f.val ∧
      ∀ v, twoFormHodgeForm u v = inner ℝ (twoFormHodgeGenerator hRic f) (twoFormH1ToL2 v) := by
  let h := (twoFormHodgeDomainEquiv hRic).symm f
  have hf : twoFormShiftedResolvent hRic h = f.val :=
    congrArg Subtype.val ((twoFormHodgeDomainEquiv hRic).apply_symm_apply f)
  refine ⟨twoFormShiftedSolution hRic h, hf, fun v => ?_⟩
  have he := twoFormShiftedSolution_weak hRic h v
  change twoFormHodgeForm (twoFormShiftedSolution hRic h) v +
    inner ℝ (twoFormShiftedResolvent hRic h) (twoFormH1ToL2 v) = _ at he
  rw [hf] at he
  change _ = inner ℝ (h - f.val) (twoFormH1ToL2 v)
  rw [inner_sub_left]
  linarith only [he]

theorem twoFormHodgeGenerator_symmetric (hRic : RicciThree g)
    (f h : twoFormHodgeDomain (o := o) hRic) :
    inner ℝ (twoFormHodgeGenerator hRic f) h.val =
      inner ℝ f.val (twoFormHodgeGenerator hRic h) := by
  obtain ⟨u, hu, he⟩ := twoFormHodgeDomain_weak hRic f
  obtain ⟨v, hv, hk⟩ := twoFormHodgeDomain_weak hRic h
  calc
    _ = twoFormHodgeForm u v := by rw [he v, hv]
    _ = twoFormHodgeForm v u := twoFormHodgeForm_comm u v
    _ = inner ℝ (twoFormHodgeGenerator hRic h) f.val := by rw [hk u, hu]
    _ = _ := real_inner_comm _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth Hodge eigenforms are total in the two-form H1 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormShiftedSolution_dense (hRic : RicciThree g) :
    DenseRange (twoFormShiftedSolution (o := o) hRic) := by
  have hr : DenseRange (twoFormRoughSolution (o := o)) :=
    adjoint_denseRange_of_injective _ (twoFormH1ToL2_injective hRic)
  exact (twoFormShiftedHodgeEquiv hRic).symm.surjective.denseRange.comp hr
    (twoFormShiftedHodgeEquiv hRic).symm.continuous

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual heat multiplier on each smooth Hodge eigensection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeat_eigenvalue (hRic : RicciThree g) (t : ℝ≥0)
    (μ : TwoFormSpectralValue (o := o) hRic) (f : TwoFormL2 o)
    (hf : f ∈ TwoFormSpectralSpace hRic μ) :
    twoFormHeat hRic t f = twoFormHeatWeight hRic t μ • f := by
  have hf' := Module.End.mem_eigenspace_iff.mp hf
  apply (twoFormSpectralEquiv hRic).injective
  apply lp.ext
  funext ν
  rw [twoFormHeat_coordinate, map_smul]
  change twoFormHeatWeight hRic t ν • (twoFormSpectralEquiv hRic f) ν =
    twoFormHeatWeight hRic t μ • (twoFormSpectralEquiv hRic f) ν
  by_cases hν : ν = μ
  · rw [hν]
  · have hne : ν.val - μ.val ≠ 0 := sub_ne_zero.mpr (fun h => hν (Subtype.ext h))
    have he := congrArg (fun u : TwoFormL2 o => (twoFormSpectralEquiv hRic u) ν) hf'
    change (twoFormSpectralEquiv hRic (twoFormShiftedResolvent hRic f)) ν =
      (twoFormSpectralEquiv hRic (μ.val • f)) ν at he
    rw [twoFormShiftedResolvent_coordinate, map_smul] at he
    have hz : (ν.val - μ.val) • (twoFormSpectralEquiv hRic f) ν = 0 := by
      rw [sub_smul, he]
      exact sub_self _
    have hv := (smul_eq_zero.mp hz).resolve_left hne
    rw [hv, smul_zero, smul_zero]

theorem twoFormHeat_eigenvector (hRic : RicciThree g) (t : ℝ≥0)
    (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormHeat hRic t (twoFormEigenvector hRic i) =
      twoFormHeatWeight hRic t i.1 • twoFormEigenvector hRic i :=
  twoFormHeat_eigenvalue hRic t i.1 _ (twoFormEigenvector_hasEigenvector hRic i).1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Bochner heat convolution, its eigenmode pairing and its
quadratic norm bound for a linearly vanishing residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHeatConvolution (hRic : RicciThree g) (R : ℝ → TwoFormL2 o) (t : ℝ) : TwoFormL2 o :=
  ∫ s in (0 : ℝ)..t, twoFormHeat hRic (t - s).toNNReal (R s)

theorem twoFormHeatConvolution_integrable (hRic : RicciThree g)
    (R : ℝ → TwoFormL2 o) (t : ℝ) (ht : 0 ≤ t) (hR : ContinuousOn R (Icc 0 t)) :
    IntervalIntegrable (fun s => twoFormHeat hRic (t - s).toNNReal (R s)) volume 0 t := by
  have htime : Continuous (fun s : ℝ => (t - s).toNNReal) :=
    continuous_real_toNNReal.comp (continuous_const.sub continuous_id)
  exact ((twoFormHeat_joint_continuous hRic).comp_continuousOn
    (htime.continuousOn.prodMk hR)).intervalIntegrable_of_Icc ht

theorem twoFormHeatConvolution_norm_le (hRic : RicciThree g)
    (R : ℝ → TwoFormL2 o) (t : ℝ) (ht : 0 ≤ t) (B : ℝ)
    (hR : ∀ s ∈ Icc 0 t, ‖R s‖ ≤ B * s) :
    ‖twoFormHeatConvolution hRic R t‖ ≤ B * t ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun s : ℝ => B * s) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, B * s := by
      apply intervalIntegral.norm_integral_le_of_norm_le ht _ hi
      exact Filter.Eventually.of_forall fun s hs =>
        (twoFormHeat_contraction hRic (t - s).toNNReal (R s)).trans
          (hR s ⟨hs.1.le, hs.2⟩)
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_id]; ring

theorem twoFormHeatConvolution_eigen (hRic : RicciThree g)
    (R : ℝ → TwoFormL2 o) (t : ℝ) (ht : 0 ≤ t) (hR : ContinuousOn R (Icc 0 t))
    (i : TwoFormEigenIndex (o := o) hRic) :
    inner ℝ (twoFormHeatConvolution hRic R t) (twoFormEigenvector hRic i) =
      ∫ s in (0 : ℝ)..t, Real.exp (-(i.1.val⁻¹ - 1) * (t - s)) *
        inner ℝ (R s) (twoFormEigenvector hRic i) := by
  have hi := twoFormHeatConvolution_integrable hRic R t ht hR
  have hp := (innerSL ℝ (twoFormEigenvector hRic i)).intervalIntegral_comp_comm hi
  change (∫ s in (0 : ℝ)..t,
    inner ℝ (twoFormEigenvector hRic i) (twoFormHeat hRic (t - s).toNNReal (R s))) =
      inner ℝ (twoFormEigenvector hRic i) (twoFormHeatConvolution hRic R t) at hp
  rw [real_inner_comm, ← hp]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht] using hs
  change inner ℝ (twoFormEigenvector hRic i) (twoFormHeat hRic (t - s).toNNReal (R s)) =
    Real.exp (-(i.1.val⁻¹ - 1) * (t - s)) * inner ℝ (R s) (twoFormEigenvector hRic i)
  rw [real_inner_comm, twoFormHeat_selfAdjoint, twoFormHeat_eigenvector, real_inner_smul_right]
  unfold twoFormHeatWeight twoFormHeatRate
  rw [Real.coe_toNNReal _ (sub_nonneg.mpr hs'.2)]
  ring_nf

end
end PositiveEinsteinFour.Geometry
end


section

/-! Degree-two de Rham cohomology of the actual smooth exterior complex,
and its harmonic representative theorem. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothClosedTwoForms
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_1
theorem smoothHarmonicToDeRham_injective (hRic : RicciThree g) :
    Function.Injective (smoothHarmonicToDeRham (o := o)) := by
  intro u v huv
  have hz : smoothHarmonicToDeRham (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hm : smoothHarmonicToClosed (u - v) ∈ smoothExactTwoForms :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  change (u - v).val ∈ LinearMap.range (smoothOneFormExteriorLinear (o := o)) at hm
  obtain ⟨a, ha⟩ := hm
  have hh : smoothOneFormExterior a ∈ smoothHarmonicTwoForms :=
    ha.symm ▸ (u - v).property
  have he : (u - v).val = 0 := ha.symm.trans (smoothHarmonic_exact_eq_zero hRic a hh)
  have he' : u - v = 0 := Subtype.ext he
  exact sub_eq_zero.mp he'

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second de Rham dimension is the sum of the two actual Hodge
eigenspace dimensions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_2
theorem smoothHarmonicPositive_star (hRic : RicciThree g)
    (u : smoothHarmonicPositive (o := o) hRic) :
    smoothHarmonicHodge hRic u.val = u.val := by
  simpa only [one_smul] using (Module.End.mem_eigenspace_iff.mp u.property)

theorem smoothHarmonicNegative_star (hRic : RicciThree g)
    (u : smoothHarmonicNegative (o := o) hRic) :
    smoothHarmonicHodge hRic u.val = -u.val := by
  simpa only [neg_one_smul] using (Module.End.mem_eigenspace_iff.mp u.property)

def smoothHarmonicSumLinear (hRic : RicciThree g) :
    (smoothHarmonicPositive (o := o) hRic × smoothHarmonicNegative (o := o) hRic)
      →ₗ[ℝ] smoothHarmonicTwoForms (o := o) where
  toFun u := u.1.val + u.2.val
  map_add' _ _ := by dsimp; abel
  map_smul' r u := by dsimp; exact (smul_add r u.1.val u.2.val).symm

theorem smoothHarmonicSumLinear_injective (hRic : RicciThree g) :
    Function.Injective (smoothHarmonicSumLinear (o := o) hRic) := by
  intro u v huv
  change u.1.val + u.2.val = v.1.val + v.2.val at huv
  have hs := congrArg (smoothHarmonicHodge hRic) huv
  simp only [map_add, smoothHarmonicPositive_star, smoothHarmonicNegative_star] at hs
  have hp : u.1.val = v.1.val := by
    calc
      u.1.val = (2 : ℝ)⁻¹ • ((u.1.val + u.2.val) + (u.1.val + -u.2.val)) := by module
      _ = (2 : ℝ)⁻¹ • ((v.1.val + v.2.val) + (v.1.val + -v.2.val)) := by rw [huv, hs]
      _ = v.1.val := by module
  have hn : u.2.val = v.2.val := add_left_cancel (hp ▸ huv)
  exact Prod.ext (Subtype.ext hp) (Subtype.ext hn)

def smoothHarmonicSumEquiv (hRic : RicciThree g) :
    (smoothHarmonicPositive (o := o) hRic × smoothHarmonicNegative (o := o) hRic)
      ≃ₗ[ℝ] smoothHarmonicTwoForms (o := o) :=
  LinearEquiv.ofBijective (smoothHarmonicSumLinear hRic)
    ⟨smoothHarmonicSumLinear_injective hRic,
      fun u => ⟨(smoothHarmonicPlus hRic u, smoothHarmonicMinus hRic u),
        smoothHarmonic_decomposition hRic u⟩⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact/coexact differential identities underlying cancellation of
the nonzero two-form spectrum in the signed trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem smoothTwoFormDDelta_hodge_DDelta (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormDDelta (smoothTwoFormHodge o (smoothTwoFormDDelta u)) = 0 := by
  have h := (smoothTwoForm_closed_iff_codifferential_hodge (smoothTwoFormDDelta u)).mp
    (smoothTwoFormDDelta_closed hRic u)
  change smoothOneFormExterior (smoothTwoFormCodifferentialField
    (smoothTwoFormHodge o (smoothTwoFormDDelta u))) = 0
  rw [h]
  exact smoothOneFormExteriorLinear.map_zero

end
end PositiveEinsteinFour.Geometry
end


section

/-! The cokernel of actual smooth divergence is measured exactly by the
scalar integral. No upper-degree index identity is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.divergenceMeanCompactFrames
def divergenceCokernelMean (o : FrameOrientation g) (hRic : RicciThree g) :
    DivergenceCokernel g →ₗ[ℝ] ℝ :=
  (LinearMap.range (smoothOneFormDivergence g)).liftQ (smoothScalarMean g o) (by
    rintro f ⟨v, rfl⟩
    exact oneFormDivergence_mean_zero (o := o) hRic v)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Hodge summand with zero Weyl curvature has no nonzero harmonic
forms. This follows from the actual integrated Weitzenbock identity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g}

local instance halfFlatHarmonicAddGroup_re876e2_1 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
local instance halfFlatNegativeAddGroup_re876e2_1 (hRic : RicciThree g) :
    AddCommGroup (smoothHarmonicNegative (o := o) hRic) := Submodule.addCommGroup _
theorem halfFlat_negative_harmonic_zero (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (u : smoothHarmonicNegative (o := o) hRic) : u = 0 := by
  have hstar (x : M) : twoFormHodge (u.val.val.val x) = -u.val.val.val x := by
    have hh := congrArg (fun v : smoothHarmonicTwoForms (o := o) => v.val.val x)
      (smoothHarmonicNegative_star hRic u)
    exact hh
  have hcurv : smoothTwoFormCurvature u.val.val = u.val.val := by
    apply Subtype.ext
    funext x
    exact halfFlat_curvature_action_negative hRic hminus x _ (hstar x)
  have hE := smoothTwoForm_Weitzenbock hRic u.val.val
  rw [smoothHarmonicTwoForm_energy_zero u.val.val u.val.property, hcurv] at hE
  have hcov := smoothTwoFormCovariantEnergy_nonneg u.val.val
  have hnorm := smoothTwoFormL2Inner_nonneg u.val.val
  have hz : smoothTwoFormL2Inner u.val.val u.val.val = 0 := by linarith
  have hform := smoothTwoFormL2Inner_definite u.val.val hz
  apply Subtype.ext
  apply Subtype.ext
  exact hform

theorem halfFlat_negative_harmonic_dimension_zero (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0) :
    Module.finrank ℝ (smoothHarmonicNegative (o := o) hRic) = 0 := by
  let : Subsingleton (smoothHarmonicNegative (o := o) hRic) :=
    ⟨fun u v => (halfFlat_negative_harmonic_zero hRic hminus u).trans
      (halfFlat_negative_harmonic_zero hRic hminus v).symm⟩
  exact Module.finrank_zero_of_subsingleton

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integral intersection pairing, its exact-form annihilator, and
its signs on the actual harmonic Hodge summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instAddCommGroupSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoFormsSmoothHarmonicTwoForms_3_re876e2_1 : AddCommGroup (smoothHarmonicTwoForms (o := o)) :=
  Submodule.addCommGroup _
theorem smoothHarmonicIntersection_positive (hRic : RicciThree g)
    (u : smoothHarmonicPositive (o := o) hRic) :
    twoFormIntersection u.val.val u.val.val = smoothTwoFormL2Inner u.val.val u.val.val := by
  have h := congrArg Subtype.val (smoothHarmonicPositive_star hRic u)
  exact congrArg (smoothTwoFormL2Inner u.val.val) h

theorem smoothHarmonicIntersection_negative (hRic : RicciThree g)
    (u : smoothHarmonicNegative (o := o) hRic) :
    twoFormIntersection u.val.val u.val.val = -smoothTwoFormL2Inner u.val.val u.val.val := by
  have h := congrArg Subtype.val (smoothHarmonicNegative_star hRic u)
  change smoothTwoFormHodge o u.val.val = -u.val.val at h
  unfold twoFormIntersection
  rw [h, smoothTwoFormL2Inner_comm, ← neg_one_smul ℝ u.val.val,
    smoothTwoFormL2Inner_smul]
  ring

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

/-! The inertia of the actual harmonic intersection form. The positive
and negative indices are the dimensions of the Hodge summands. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.harmonicSignatureAddGroup
theorem harmonicIntersection_positive_definite (hRic : RicciThree g) :
    ((harmonicIntersectionQuadratic (o := o)).restrict
      (smoothHarmonicPositive hRic)).PosDef := by
  intro u hu
  change 0 < twoFormIntersection u.val.val u.val.val
  rw [smoothHarmonicIntersection_positive hRic u]
  apply lt_of_le_of_ne (smoothTwoFormL2Inner_nonneg _)
  intro hz
  apply hu
  exact Subtype.ext (Subtype.ext (smoothTwoFormL2Inner_definite _ hz.symm))

theorem harmonicIntersection_negative_definite (hRic : RicciThree g) :
    ((-harmonicIntersectionQuadratic (o := o)).restrict
      (smoothHarmonicNegative hRic)).PosDef := by
  intro u hu
  change 0 < -twoFormIntersection u.val.val u.val.val
  rw [smoothHarmonicIntersection_negative hRic u, neg_neg]
  apply lt_of_le_of_ne (smoothTwoFormL2Inner_nonneg _)
  intro hz
  apply hu
  exact Subtype.ext (Subtype.ext (smoothTwoFormL2Inner_definite _ hz.symm))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual infinite spectral kernel has the expected integrated
diagonal trace. Absolute convergence justifies both exchanges. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHeatWeight_half_sq (hRic : RicciThree g) (t : ℝ≥0)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    twoFormHeatWeight hRic (t / 2) μ ^ 2 = twoFormHeatWeight hRic t μ := by
  simp only [twoFormHeatWeight, pow_two, ← Real.exp_add, NNReal.coe_div, NNReal.coe_ofNat]
  congr 1
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact H1 realizations of smooth two-form heat outputs and coexact lifts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g)

theorem twoFormHeatLift_smooth (t : ℝ≥0) (ht : 0 < t) (f : TwoFormL2 o)
    (u : smoothTwoForms o) (hu : twoFormHeat hRic t f = smoothTwoFormToL2 (u : SmoothL2TwoForm o)) :
    twoFormHeatLift hRic t ht f = smoothTwoFormToH1 (u : SmoothH1TwoForm o) := by
  apply twoFormH1ToL2_injective hRic
  rw [twoFormHeatLift_value]
  exact hu.trans (twoFormH1ToL2_smooth (u : SmoothH1TwoForm o)).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar spectral pairing of the actual heat operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormEigenbasis_apply (hRic : RicciThree g)
    (i : TwoFormEigenIndex (o := o) hRic) :
    twoFormEigenbasis hRic i = twoFormEigenvector hRic i := by
  simp only [twoFormEigenbasis, HilbertBasis.coe_mk]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 spectral heat column with one frame and component fixed.
Square summability follows from the proved positive-time diagonal estimate. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff Manifold _root_.Topology NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoForm_eq_of_eigen_pairing (hRic : RicciThree g) (v w : TwoFormL2 o)
    (h : ∀ i : TwoFormEigenIndex (o := o) hRic,
      inner ℝ v (twoFormEigenvector hRic i) = inner ℝ w (twoFormEigenvector hRic i)) : v = w := by
  apply (twoFormEigenbasis hRic).repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply, twoFormEigenbasis_apply]
  exact (real_inner_comm _ _).trans ((h i).trans (real_inner_comm _ _))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact grouping of the scalar, one-form and two-form heat traces
by the finite eigenspaces of the actual shifted resolvents. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarHeatSpectralTrace (t : ℝ≥0) : ℝ := ∑' i, scalarBaseHeatWeight g o d t i

def twoFormHeatSpectralTrace (t : ℝ≥0) : ℝ :=
  ∑' i : TwoFormEigenIndex (o := o) hRic, twoFormHeatWeight hRic t i.1

def oneFormExactHeatTrace (t : ℝ≥0) : ℝ :=
  ∑' i : OneFormExactEigenIndex g o d, scalarBaseHeatWeight g o d t i.val

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic Hodge-signed diagonal trace of the actual heat kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_hodge_pairing_integral (u : smoothTwoForms o) :
    (∫ x, inner ℝ (u.val x) (twoFormHodge (u.val x)) ∂normalizedVolume g) =
      inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o))
        (twoFormL2Hodge (smoothTwoFormToL2 (u : SmoothL2TwoForm o))) := by
  calc
    _ = inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o))
        (smoothTwoFormToL2 (smoothL2Hodge (u : SmoothL2TwoForm o))) :=
      (smoothTwoFormToL2_inner (u : SmoothL2TwoForm o)
        (smoothL2Hodge (u : SmoothL2TwoForm o))).symm
    _ = _ := congrArg (fun a : TwoFormL2 o =>
      inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o)) a)
        (twoFormL2Hodge_smooth (u : SmoothL2TwoForm o)).symm

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

theorem heatNormalOneResidualColumn_component (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (l k : Fin 4) (x : FourSpace) :
    heatNormalOneResidualColumn E χ t l x k =
      deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
        fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k := by
  change heatNormalOneTimeColumn E χ t l x k + _ = _
  rw [heatNormalOneTimeColumn_component E χ t ht l k x]
  rfl

theorem heatNormalOneResidualColumn_bound (E : HeatNormalOneExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (B : ℝ)
    (h : ∀ x k l, |deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t +
      fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalOneCutoffParametrix E χ t y q l) x k| ≤ B * t)
    (l : Fin 4) (x : FourSpace) : ‖heatNormalOneResidualColumn E χ t l x‖ ≤ 4 * (B * t) := by
  calc
    _ ≤ ∑ k, |heatNormalOneResidualColumn E χ t l x k| := fourSpace_norm_le_sum _
    _ ≤ ∑ _k : Fin 4, B * t := Finset.sum_le_sum fun k _ => by
      rw [heatNormalOneResidualColumn_component E χ t ht l k x]
      exact h x k l
    _ = _ := by simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global compact parametrix has the actual initial delta pairing
against every smooth two-form. The normalized measure factor is explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalGlobalParametrixColumn_initial (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (hχ0 : χ 0 = 1) (l : Fin 6)
    (v : SmoothL2TwoForm o) :
    Tendsto (fun t => inner ℝ (heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs t l)
        (smoothTwoFormToL2 v)) (𝓝[Ioi 0] 0)
      (𝓝 ((normalizedChartFactor g).toReal *
        heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val 0 l)) := by
  let V := heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val
  let f := fun k x => frameExponentialJacobian g o e x * V x k
  have hV : ContinuousOn V C.source := by
    intro x hx
    exact (heatNormalTwoFormValue_contDiffAt 2 (v : smoothTwoForms o).property c D.point x
      (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx))).continuousAt.continuousWithinAt
  have hf (k : Fin 6) : ContinuousOn (f k) C.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      ((EuclideanSpace.proj k).continuous.comp_continuousOn hV)
  have hχf (k : Fin 6) : Continuous (fun x => χ x * f k x) :=
    heat_continuous_mul_of_tsupport_subset hχ.continuous C.open_source (hf k) hs
  have hi (t : ℝ) (k : Fin 6) :
      Integrable (fun x => heatNormalCutoffParametrix E χ t x k l * f k x) := by
    have hcont := (hχf k).mul (heatNormalBundleParametrix_space_regular E t k l).continuous
    have hint : Integrable (fun x => (χ x * f k x) *
        heatNormalBundleParametrix E t x k l) :=
      hcont.integrable_of_hasCompactSupport ((hc.mul_right).mul_right)
    convert hint using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    dsimp only [heatNormalCutoffParametrix]
    ring
  have hp (t : ℝ) :
      inner ℝ (heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs t l)
        (smoothTwoFormToL2 v) =
      (normalizedChartFactor g).toReal *
        ∑ k : Fin 6, ∫ x, heatNormalCutoffParametrix E χ t x k l * f k x := by
    have hpair := heatNormalAmplitudeL2_pairing_normal D C hE hCt hP hD
      (heatNormalCutoffColumn E χ t l) (heatNormalCutoffColumn_regular E χ hχ t l)
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E χ t l))
      ((heatNormalCutoffColumn_support E χ t l).trans hs) v
    apply hpair.trans
    congr 1
    calc
      _ = ∫ x, ∑ k : Fin 6, heatNormalCutoffParametrix E χ t x k l * f k x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          simp only [PiLp.inner_apply, heatNormalCutoffColumn, f, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          change frameExponentialJacobian g o e x *
            (V x k * heatNormalCutoffParametrix E χ t x k l) =
            heatNormalCutoffParametrix E χ t x k l * (frameExponentialJacobian g o e x * V x k)
          ring
      _ = _ := integral_finsetSum _ (fun k _ => hi t k)
  have ht := (tendsto_finsetSum Finset.univ fun k _ =>
    heatNormalCutoffParametrix_initial_local E χ (f k) (hχf k) hc hχ0 k l).const_mul
      (normalizedChartFactor g).toReal
  have hz : (∑ k : Fin 6, (if k = l then 1 else 0) * f k 0) = V 0 l := by
    simp [f, frameExponentialJacobian_zero]
  rw [hz] at ht
  exact ht.congr' (Eventually.of_forall fun t => (hp t).symm)

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

theorem heatNormalCutoffParametrix_pairing_deriv (E : HeatNormalBundleExtension D)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hc : HasCompactSupport χ) (t : ℝ) (ht : 0 < t) (k l : Fin 6) :
    HasDerivAt (fun s => ∫ x, heatNormalCutoffParametrix E χ s x k l * f x)
      (∫ x, deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t * f x) t := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => E.amplitude m x k l
  have h := fourHeat_compact_polynomial_pairing_deriv (fun x => χ x * f x) hχf hc.mul_right
    u (fun m => (E.amplitude_regular m (by omega) k l).continuous) t ht
  have hfun : (fun s => ∫ x, (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x)) =
      fun s => ∫ x, heatNormalCutoffParametrix E χ s x k l * f x := by
    funext s
    apply integral_congr_ae
    filter_upwards [] with x
    change (χ x * f x) * (fourHeatGaussian s x * fourHeatPolynomial u s x) =
      (χ x * (fourHeatGaussian s x * fourHeatPolynomial u s x)) * f x
    ring
  have hval : (∫ x, (χ x * f x) * fourHeatGaussianPolynomialTime u t x) =
      ∫ x, deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t * f x := by
    apply integral_congr_ae
    filter_upwards [] with x
    have hd := (fourHeatGaussianPolynomial_hasDerivAt u t ht x).const_mul (χ x)
    change HasDerivAt (fun s => heatNormalCutoffParametrix E χ s x k l)
      (χ x * fourHeatGaussianPolynomialTime u t x) t at hd
    rw [hd.deriv]
    ring
  rwa [hfun, hval] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-frame coefficients satisfy every hypothesis of
the finite-regularity Green identity on a proved neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.green_regular_near (D : HeatNormalFrameData g o c e) :
    ∀ᶠ x in 𝓝 (0 : FourSpace),
      (∀ i k l, ContDiffAt ℝ 1 (fun y => heatTwoFormConnection g c D.point i y k l) x) ∧
      (∀ i j, ContDiffAt ℝ 1 (fun y => (heatNormalMetric g o e y)⁻¹ i j) x) ∧
      ContDiffAt ℝ 1 (frameExponentialJacobian g o e) x ∧
      0 < frameExponentialJacobian g o e x ∧
      (∀ k l, ContinuousAt (fun y => heatNormalPotential g c D.point y k l) x) := by
  have hA := eventually_all.mpr fun i => eventually_all.mpr fun k =>
    eventually_all.mpr fun l => ((D.twoForm_connection_regular i k l).of_le
      (show (1 : ℕ∞ω) ≤ 11 by norm_num)).eventually (by norm_num)
  have ha := eventually_all.mpr fun i => eventually_all.mpr fun j =>
    ((heatNormalInverse_smoothAt_zero g o e i j).of_le
      (show (1 : ℕ∞ω) ≤ ∞ by first | simp | exact_mod_cast le_top)).eventually (by norm_num)
  have hρ := ((frameExponentialJacobian_smoothAt_zero g o e).of_le
    (show (1 : ℕ∞ω) ≤ ∞ by first | simp | exact_mod_cast le_top)).eventually (by norm_num)
  have hV := eventually_all.mpr fun k => eventually_all.mpr fun l =>
    ((D.potential_regular k l).of_le (show (1 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  filter_upwards [hA, ha, hρ, frameExponentialJacobian_eventually_pos g o e, hV]
    with x hxA hxa hxρ hxpos hxV
  exact ⟨hxA, hxa, hxρ, hxpos, fun k l => (hxV k l).continuousAt⟩

theorem HeatNormalBundleExtension.connection_operator_near
    {D : HeatNormalFrameData g o c e} (E : HeatNormalBundleExtension D) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ u : FourSpace → Fin 6 → ℝ,
      (∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) → ∀ k,
      fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x) u x k =
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) u x k := by
  filter_upwards [E.base.a_near, E.base.b_near, E.B_near, E.C_near, D.green_regular_near]
    with x ha hb hB hC hreg
  intro u hu k
  rw [ha, hb, hB, hC]
  exact (heatNormalConnectionOperator_eq D u x
    (fun i k l => (hreg.1 i k l).differentiableAt one_ne_zero) hu k).symm

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

theorem heatNormalTimeColumn_component (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (l k : Fin 6) (x : FourSpace) :
    heatNormalTimeColumn E χ t l x k =
      deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t :=
  ((fourHeatGaussianPolynomial_hasDerivAt (fun m y => E.amplitude m y k l) t ht x).const_mul
    (χ x)).deriv.symm

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def heatNormalGlobalTimeColumn (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalAmplitudeL2 D C hCt hP hD (heatNormalTimeColumn E χ t l)
    (heatNormalTimeColumn_regular E χ hχ t l)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalTimeColumn_support E χ t l))
    ((heatNormalTimeColumn_support E χ t l).trans hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Correct normalization of the compact parametrix for the actual
probability measure used by the spectral Hodge heat kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {D : HeatNormalFrameData g o c e}

theorem heatNormalizedParametrixColumn_initial (E : HeatNormalBundleExtension D)
    (he : e.base ∈ (chartAt FourSpace c).source)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (hχ0 : χ 0 = 1) (l : Fin 6)
    (v : SmoothL2TwoForm o) :
    Tendsto (fun t => inner ℝ (heatNormalizedParametrixColumn E C hCt hP hD χ hχ hc hs t l)
        (smoothTwoFormToL2 v)) (𝓝[Ioi 0] 0)
      (𝓝 (twoFormFrameValue o (v : smoothTwoForms o).val e l)) := by
  have h0 := heatNormalGlobalParametrixColumn_initial E C hE hCt hP hD χ hχ hc hs hχ0 l v
  have h := h0.const_mul ((normalizedChartFactor g).toReal)⁻¹
  have hn : (normalizedChartFactor g).toReal ≠ 0 := (normalizedChartFactor_toReal_pos g).ne'
  rw [D.value_zero he, ← mul_assoc, inv_mul_cancel₀ hn, one_mul] at h
  simpa only [heatNormalizedParametrixColumn, real_inner_smul_left] using h

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

theorem heatNormalTimeColumn_joint_continuousOn (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (l : Fin 6) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalTimeColumn E χ z.1 l z.2)
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

/-! Genuine normal one-form coefficients on one common Green-identity neighborhood. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.oneGreen_regular_near (D : HeatNormalFrameData g o c e) :
    ∀ᶠ x in 𝓝 (0 : FourSpace),
      (∀ i k l, ContDiffAt ℝ 1 (fun y => heatNormalFrameConnection g c D.point i y k l) x) ∧
      (∀ i j, ContDiffAt ℝ 1 (fun y => (heatNormalMetric g o e y)⁻¹ i j) x) ∧
      ContDiffAt ℝ 1 (frameExponentialJacobian g o e) x ∧
      0 < frameExponentialJacobian g o e x := by
  have hA := eventually_all.mpr fun i => eventually_all.mpr fun k =>
    eventually_all.mpr fun l => ((D.connection_regular i k l).of_le
      (show (1 : ℕ∞ω) ≤ 11 by norm_num)).eventually (by norm_num)
  filter_upwards [hA, D.green_regular_near] with x hxA hx
  exact ⟨hxA, hx.2.1, hx.2.2.1, hx.2.2.2.1⟩

theorem HeatNormalOneExtension.connection_operator_near
    {D : HeatNormalFrameData g o c e} (E : HeatNormalOneExtension D) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ u : FourSpace → Fin 4 → ℝ,
      (∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) → ∀ k,
      fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x) u x k =
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c D.point) ((3 : ℝ) • (1 : Mat4)) u x k := by
  filter_upwards [E.base.a_near, E.base.b_near, E.B_near, E.C_near, D.oneGreen_regular_near]
    with x ha hb hB hC hreg
  intro u hu k
  rw [ha, hb, hB, hC]
  unfold heatNormalOneFirst heatNormalOneZero
  exact (fourHeatOneCovariantOperator_eq _ _ _ _ _ x
    (fun i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun i k l => (hreg.1 i k l).differentiableAt one_ne_zero) hu k).symm

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatNormalFrameData.actual_one_operator_uniform_near
    (D : HeatNormalFrameData g o c e) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∀ᶠ x in 𝓝 (0 : FourSpace), ∀ u : smoothCovariantFields M 1, ∀ k : Fin 4,
      fourHeatOneOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalOneFirst D x) (heatNormalOneZero D x)
        (heatNormalOneFormValue c D.point u) x k =
      heatNormalOneFormValue c D.point (smoothOneFormHodgeLaplacian (o := o) u) x k := by
  obtain ⟨r, C, hr, hCs, hE, _hI, hCt, hP, hD⟩ := exists_heatNormalFrameChart D he
  filter_upwards [hCs ▸ ball_mem_nhds (0 : FourSpace) hr,
    frameExponentialJacobian_eventually_pos g o e] with x hx hpos
  intro u k
  apply D.actual_one_operator_at hRic x (hD hx)
    ((hP.contDiffAt (C.open_source.mem_nhds hx)).of_le (by norm_num))
    (by rw [← hE hx]; exact hCt (C.map_source hx)) _ u k
  exact Real.sqrt_pos.mp hpos

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

theorem heatNormalResidualColumn_component (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (l k : Fin 6) (x : FourSpace) :
    heatNormalResidualColumn E χ t l x k =
      deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
        fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
          (fun y q => heatNormalCutoffParametrix E χ t y q l) x k := by
  change heatNormalTimeColumn E χ t l x k + _ = _
  rw [heatNormalTimeColumn_component E χ t ht l k x]
  rfl

theorem heatNormalResidualColumn_regular (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (t : ℝ) (l : Fin 6) :
    ContDiff ℝ 2 (heatNormalResidualColumn E χ t l) :=
  (heatNormalTimeColumn_regular E χ (hχ.of_le (by norm_num)) t l).add
    (heatNormalOperatorAmplitude_regular E _ (heatNormalCutoffColumn_regular_four E χ hχ t l))

theorem heatNormalResidualColumn_support (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (l : Fin 6) :
    tsupport (heatNormalResidualColumn E χ t l) ⊆ tsupport χ :=
  (tsupport_add _ _).trans (union_subset (heatNormalTimeColumn_support E χ t l)
    ((heatNormalOperatorAmplitude_support E _).trans (heatNormalCutoffColumn_support E χ t l)))

theorem heatNormalResidualColumn_bound (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ x k l, |deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t +
      fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalCutoffParametrix E χ t y q l) x k| ≤ B * t)
    (l : Fin 6) (x : FourSpace) : ‖heatNormalResidualColumn E χ t l x‖ ≤ 3 * (B * t) := by
  apply heat_six_norm_le _ _ (mul_nonneg hB ht.le)
  intro k
  rw [heatNormalResidualColumn_component E χ t ht l k x]
  exact h x k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed zeroth-order coefficient is purely quadratic in the
connection: the potential and the linear connection terms have zero trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem HeatNormalFrameData.bundleZero_signed_near (D : HeatNormalFrameData g o c e) :
    (fun x => (twoFormHodgeMatrix * heatNormalBundleZero D x).trace) =ᶠ[𝓝 0]
      (fun x => -heatNormalConnectionQuadratic (D := D)
        (fun y => (heatNormalMetric g o e y)⁻¹) x) := by
  filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos, D.green_regular_near]
    with x hx hreg
  apply heatConnectionZero_signed_trace
  · rw [D.potential_as_actual x hx]
    exact heat_actual_potential_signed_trace _
  · intro i
    exact heatTwoFormConnectionMatrix_signed_trace _
  · intro i j
    exact D.connection_partial_signed_trace x i j
      (fun k l => (hreg.1 i k l).differentiableAt one_ne_zero)

theorem HeatNormalBundleExtension.C_signed_near {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) :
    (fun x => (twoFormHodgeMatrix * E.C x).trace) =ᶠ[𝓝 0]
      (fun x => -heatNormalConnectionQuadratic (D := D) E.base.a x) := by
  filter_upwards [E.C_near, E.base.a_near, D.bundleZero_signed_near] with x hC ha hs
  rw [hC, hs]
  simp only [heatNormalConnectionQuadratic, ha]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact normal amplitude satisfies Green's identity against
every actual smooth two-form on one fixed geometric neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.compact_green_near
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ (a : FourSpace → TwoFormFour), ContDiff ℝ 2 a →
      HasCompactSupport a → tsupport a ⊆ ball 0 r → ∀ v : smoothTwoForms o,
      (∫ x, frameExponentialJacobian g o e x *
        inner ℝ (a x) (heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic v).val x)) =
      ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (heatNormalOperatorAmplitude E a x) (heatNormalTwoFormValue o c D.point v.val x) := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hn := D.green_regular_near.and (E.connection_operator_near.and
    ((D.actual_bundle_operator_uniform_near he hRic).and
      (hp.and (ball_mem_nhds (0 : FourSpace) D.radius_pos))))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro a ha hc hs v
  let u := fun x k => a x k
  let w := fun x k => heatNormalTwoFormValue o c D.point v.val x k
  have hu (k : Fin 6) : ContDiff ℝ 2 (fun x => u x k) :=
    (contDiff_piLp (p := 2)).mp ha k
  have hsc (k : Fin 6) : tsupport (fun x => u x k) ⊆ ball 0 r :=
    (heatAmplitude_component_support a k).trans hs
  have hcc (k : Fin 6) : HasCompactSupport (fun x => u x k) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (heatAmplitude_component_support a k)
  have hw (x : FourSpace) (hx : x ∈ ball 0 r) (k : Fin 6) :
      ContDiffAt ℝ 2 (fun y => w y k) x := by
    have h := heatNormalTwoFormValue_contDiffAt 2 v.property c D.point x
      (hball hx).2.2.2.1 (D.in_chart x (hball hx).2.2.2.2)
    exact (contDiffAt_piLp (p := 2)).mp h k
  have hop (x : FourSpace) (k : Fin 6) : heatNormalOperatorAmplitude E a x k =
      fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) u x k :=
    E.compact_operator_eq (ball 0 r) (fun y hy => (hball hy).2.1) a ha hs x k
  have htest (x : FourSpace) : frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic v).val x) =
      ∑ k : Fin 6, frameExponentialJacobian g o e x * u x k *
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) w x k := by
    rw [heat_weighted_inner_sum]
    by_cases hx : x ∈ ball 0 r
    · apply Finset.sum_congr rfl
      intro k _
      have hactual := (hball hx).2.2.1 v (hball hx).2.2.2.2 k
      have hconv := heatNormalConnectionOperator_eq D w x
        (fun i k l => ((hball hx).1.1 i k l).differentiableAt one_ne_zero) (hw x hx) k
      rw [← hconv] at hactual
      rw [hactual]
    · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      have hzk (k : Fin 6) : u x k = 0 := by change a x k = 0; rw [hz]; rfl
      simp only [hz, PiLp.zero_apply, hzk, mul_zero, zero_mul, Finset.sum_const_zero]
  have hg := fourHeatCovariantOperator_compact_adjoint
    (heatTwoFormConnection g c D.point) (fun x => (heatNormalMetric g o e x)⁻¹)
    (frameExponentialJacobian g o e) (heatNormalPotential g c D.point) u w (ball 0 r)
    hu hcc hsc hw (fun x hx => (hball hx).1.1) (fun x hx => (hball hx).1.2.1)
    (fun x hx => (hball hx).1.2.2.1) (fun x hx => (hball hx).1.2.2.2.1.ne')
    (fun x hx => (hball hx).1.2.2.2.2)
    (fun _ _ i => heatTwoFormConnectionMatrix_skew _)
    (fun x _ i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun x hx => D.potential_symmetric x (hball hx).2.2.2.2)
  calc
    _ = ∫ x, ∑ k : Fin 6, frameExponentialJacobian g o e x * u x k *
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) w x k := by
      apply integral_congr_ae
      exact Eventually.of_forall htest
    _ = _ := hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heat_weighted_inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hop]
      ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact component-integral pairing for compact normal amplitudes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalAmplitudeL2_pairing_sum
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : SmoothL2TwoForm o) :
    inner ℝ (heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothTwoFormToL2 v) =
      (normalizedChartFactor g).toReal * ∑ k : Fin 6, ∫ x,
        a x k * (frameExponentialJacobian g o e x *
          heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val x k) := by
  let f := fun k x => frameExponentialJacobian g o e x *
    heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val x k
  have hV : ContinuousOn (heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val)
      C.source := by
    intro x hx
    exact (heatNormalTwoFormValue_contDiffAt 2 (v : smoothTwoForms o).property c D.point x
      (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx))).continuousAt.continuousWithinAt
  have hf (k : Fin 6) : ContinuousOn (f k) C.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      ((EuclideanSpace.proj k).continuous.comp_continuousOn hV)
  have hi (k : Fin 6) : Integrable (fun x => a x k * f k x) := by
    have hak := ((contDiff_piLp (p := 2)).mp ha k).continuous
    have hck : HasCompactSupport (fun x => a x k) :=
      hc.of_isClosed_subset (isClosed_tsupport _) (heatAmplitude_component_support a k)
    have hfk (x : FourSpace) (hx : x ∈ tsupport (fun y => a y k)) : ContinuousAt (f k) x :=
      (hf k).continuousAt (C.open_source.mem_nhds (hs (heatAmplitude_component_support a k hx)))
    simpa only [mul_comm] using fourHeat_local_product_integrable (f k) (fun x => a x k) hak hck hfk
  have hpair := heatNormalAmplitudeL2_pairing_normal D C hE hCt hP hD a ha hc hs v
  apply hpair.trans
  congr 1
  calc
    _ = ∫ x, ∑ k : Fin 6, a x k * f k x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [PiLp.inner_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      change frameExponentialJacobian g o e x *
        (heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val x k * a x k) = _
      dsimp only [f]
      ring
    _ = _ := integral_finsetSum _ (fun k _ => hi k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual compact one-form amplitudes satisfy the geometric Green identity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.compact_green_near
    (E : HeatNormalOneExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ (a : FourSpace → FourSpace), ContDiff ℝ 2 a →
      HasCompactSupport a → tsupport a ⊆ ball 0 r → ∀ v : smoothCovariantFields M 1,
      (∫ x, frameExponentialJacobian g o e x *
        inner ℝ (a x) (heatNormalOneValue c D.point (smoothOneFormHodgeLaplacian (o := o) v) x)) =
      ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (heatNormalOneOperatorAmplitude E a x) (heatNormalOneValue c D.point v x) := by
  have hp : ∀ᶠ x in 𝓝 (0 : FourSpace), ContDiffAt ℝ 2 D.point x :=
    (D.regular.of_le (show (2 : ℕ∞ω) ≤ 12 by norm_num)).eventually (by norm_num)
  have hn := D.oneGreen_regular_near.and (E.connection_operator_near.and
    ((D.actual_one_operator_uniform_near he hRic).and
      (hp.and (ball_mem_nhds (0 : FourSpace) D.radius_pos))))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨r, hr, ?_⟩
  intro a ha hc hs v
  let u := fun x k => a x k
  let w := fun x k => heatNormalOneFormValue c D.point v x k
  have hu (k : Fin 4) : ContDiff ℝ 2 (fun x => u x k) :=
    (contDiff_piLp (p := 2)).mp ha k
  have hsc (k : Fin 4) : tsupport (fun x => u x k) ⊆ ball 0 r :=
    (heatOneAmplitude_component_support a k).trans hs
  have hcc (k : Fin 4) : HasCompactSupport (fun x => u x k) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (heatOneAmplitude_component_support a k)
  have hw (x : FourSpace) (hx : x ∈ ball 0 r) (k : Fin 4) :
      ContDiffAt ℝ 2 (fun y => w y k) x := by
    exact heatNormalOneFormValue_regular 2 c D.point v x
      (hball hx).2.2.2.1 (D.in_chart x (hball hx).2.2.2.2) k
  have hop (x : FourSpace) (k : Fin 4) : heatNormalOneOperatorAmplitude E a x k =
      fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4))) u x k :=
    E.compact_operator_eq (ball 0 r) (fun y hy => (hball hy).2.1) a ha hs x k
  have htest (x : FourSpace) : frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalOneValue c D.point (smoothOneFormHodgeLaplacian (o := o) v) x) =
      ∑ k : Fin 4, frameExponentialJacobian g o e x * u x k *
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4))) w x k := by
    rw [heat_one_weighted_inner_sum]
    by_cases hx : x ∈ ball 0 r
    · apply Finset.sum_congr rfl
      intro k _
      have hactual := (hball hx).2.2.1 v k
      have hconv := fourHeatOneCovariantOperator_eq
        (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalFrameConnection g c D.point) ((3 : ℝ) • (1 : Mat4)) w x
        (fun i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
        (fun i k l => ((hball hx).1.1 i k l).differentiableAt one_ne_zero) (hw x hx) k
      unfold heatNormalOneFirst heatNormalOneZero at hactual
      rw [← hconv] at hactual
      rw [hactual]
      rfl
    · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      have hzk (k : Fin 4) : u x k = 0 := by change a x k = 0; rw [hz]; rfl
      simp only [hz, PiLp.zero_apply, hzk, mul_zero, zero_mul, Finset.sum_const_zero]
  have hg := fourHeatOneCovariantOperator_compact_adjoint
    (heatNormalFrameConnection g c D.point) (fun x => (heatNormalMetric g o e x)⁻¹)
    (frameExponentialJacobian g o e) ((fun _ : FourSpace => (3 : ℝ) • (1 : Mat4))) u w (ball 0 r)
    hu hcc hsc hw (fun x hx => (hball hx).1.1) (fun x hx => (hball hx).1.2.1)
    (fun x hx => (hball hx).1.2.2.1) (fun x hx => (hball hx).1.2.2.2.ne')
    (fun _ _ _ _ => continuousAt_const)
    (fun x hx i => D.connection_skew x (hball hx).2.2.2.2 i)
    (fun x _ i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun _ _ k l => by simp [Matrix.one_apply, eq_comm])
  calc
    _ = ∫ x, ∑ k : Fin 4, frameExponentialJacobian g o e x * u x k *
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4))) w x k := by
      apply integral_congr_ae
      exact Eventually.of_forall htest
    _ = _ := hg
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heat_one_weighted_inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hop]
      change _ = _ * _ * w x k
      ring


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

theorem heatNormalOperatorColumn_joint_continuousOn (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (l : Fin 6) :
    ContinuousOn (fun z : ℝ × FourSpace =>
      heatNormalOperatorAmplitude E (heatNormalCutoffColumn E χ z.1 l) z.2)
      (Ioi 0 ×ˢ univ) := by
  apply (PiLp.continuous_toLp 2 _).comp_continuousOn
  apply continuousOn_pi.mpr
  intro k z hz
  exact (fourHeatBundleOperator_joint_continuousAt E.base.a E.base.b E.B E.C
    (fun w k => heatNormalCutoffParametrix E χ w.1 w.2 k l) z
    (fun i j => (E.base.a_regular i j).continuous.continuousAt)
    (fun i => (E.base.b_regular i).continuous.continuousAt)
    (fun i k l => (E.B_regular i k l).continuous.continuousAt)
    (fun k l => (E.C_regular k l).continuous.continuousAt)
    (fun k => heatNormalCutoffParametrix_joint_contDiffAt E χ hχ z hz.1 k l) k).continuousWithinAt

theorem heatNormalResidualColumn_joint_continuousOn (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (l : Fin 6) :
    ContinuousOn (fun z : ℝ × FourSpace => heatNormalResidualColumn E χ z.1 l z.2)
      (Ioi 0 ×ˢ univ) :=
  (heatNormalTimeColumn_joint_continuousOn E χ hχ.continuous l).add
    (heatNormalOperatorColumn_joint_continuousOn E χ hχ l)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The source of the first radial amplitude has a signed trace equal
to the leading scalar amplitude times the quadratic connection term. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.firstSource_signed_near (E : HeatNormalBundleExtension D) :
    (fun x => (twoFormHodgeMatrix * E.firstSource x).trace) =ᶠ[𝓝 0]
      (fun x => E.base.U x * heatNormalConnectionQuadratic (D := D) E.base.a x) := by
  filter_upwards [E.B_signed_near, E.C_signed_near] with x hB hC
  change (twoFormHodgeMatrix * (show HeatMat6 from fun k l =>
    -fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
      (fun y q => E.base.U y * (if q = l then 1 else 0)) x k)).trace = _
  rw [fourHeat_leading_signed_source _ _ _ _ _ x hB, hC]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual L2 image of the compact one-form coefficient operator,
with its distributional identity against every smooth test section. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.compact_operator_pairing_near
    (E : HeatNormalOneExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (hRic : RicciThree g) :
    ∃ r > (0 : ℝ), ∀ (C : OpenPartialHomeomorph FourSpace M)
      (_hE : EqOn C (frameExponential g o e) C.source)
      (hCt : C.target ⊆ (chartAt FourSpace c).source)
      (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
      (a : FourSpace → FourSpace) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
      (hs : tsupport a ⊆ C.source), tsupport a ⊆ Metric.ball 0 r →
      ∀ v : smoothCovariantFields M 1,
        inner ℝ (heatNormalOneAmplitudeL2 D C hCt hP hD a (ha.of_le (by norm_num)) hc hs)
          (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (heatNormalOneHodgeImage E C hCt hP hD a ha hc hs)
          (smoothOneFormL2Linear v) := by
  obtain ⟨r, hr, hgreen⟩ := E.compact_green_near he hRic
  refine ⟨r, hr, ?_⟩
  intro C hE hCt hP hD a ha hc hs hsmall v
  have hleft := heatNormalOneAmplitudeL2_pairing_normal D C hE hCt hP hD a
    (ha.of_le (by norm_num)) hc hs (smoothOneFormHodgeLaplacian (o := o) v)
  have hright := heatNormalOneAmplitudeL2_pairing_normal D C hE hCt hP hD
    (heatNormalOneOperatorAmplitude E a) (heatNormalOneOperatorAmplitude_regular E a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneOperatorAmplitude_support E a))
    ((heatNormalOneOperatorAmplitude_support E a).trans hs) v
  exact hleft.trans ((congrArg ((normalizedChartFactor g).toReal * ·)
    (hgreen a (ha.of_le (by norm_num)) hc hsmall v)).trans hright.symm)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Weak time differentiation of the actual global parametrix, with its
derivative represented by the constructed global L2 time column. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem heatNormalGlobalParametrixColumn_weak_deriv (E : HeatNormalBundleExtension D)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (ht : 0 < t) (l : Fin 6)
    (v : SmoothL2TwoForm o) :
    HasDerivAt (fun s => inner ℝ (heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs s l)
        (smoothTwoFormToL2 v))
      (inner ℝ (heatNormalGlobalTimeColumn E C hCt hP hD χ hχ hc hs t l)
        (smoothTwoFormToL2 v)) t := by
  let f := fun k x => frameExponentialJacobian g o e x *
    heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val x k
  have hV : ContinuousOn (heatNormalTwoFormValue o c D.point (v : smoothTwoForms o).val)
      C.source := by
    intro x hx
    exact (heatNormalTwoFormValue_contDiffAt 2 (v : smoothTwoForms o).property c D.point x
      (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx))).continuousAt.continuousWithinAt
  have hf (k : Fin 6) : ContinuousOn (f k) C.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      ((EuclideanSpace.proj k).continuous.comp_continuousOn hV)
  have hχf (k : Fin 6) : Continuous (fun x => χ x * f k x) :=
    heat_continuous_mul_of_tsupport_subset hχ.continuous C.open_source (hf k) hs
  have hd := (HasDerivAt.sum (u := Finset.univ) fun k _ =>
    heatNormalCutoffParametrix_pairing_deriv E χ (f k) (hχf k) hc t ht k l).const_mul
      (normalizedChartFactor g).toReal
  have hfun : (fun s => inner ℝ (heatNormalGlobalParametrixColumn E C hCt hP hD χ hχ hc hs s l)
      (smoothTwoFormToL2 v)) = fun s => (normalizedChartFactor g).toReal *
        ∑ k : Fin 6, ∫ x, heatNormalCutoffParametrix E χ s x k l * f k x := by
    funext s
    exact heatNormalAmplitudeL2_pairing_sum C hE hCt hP hD (heatNormalCutoffColumn E χ s l)
      (heatNormalCutoffColumn_regular E χ hχ s l)
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalCutoffColumn_support E χ s l))
      ((heatNormalCutoffColumn_support E χ s l).trans hs) v
  have hval : inner ℝ (heatNormalGlobalTimeColumn E C hCt hP hD χ hχ hc hs t l)
      (smoothTwoFormToL2 v) = (normalizedChartFactor g).toReal *
        ∑ k : Fin 6, ∫ x, deriv (fun s => heatNormalCutoffParametrix E χ s x k l) t * f k x := by
    have hpair := heatNormalAmplitudeL2_pairing_sum C hE hCt hP hD (heatNormalTimeColumn E χ t l)
      (heatNormalTimeColumn_regular E χ hχ t l)
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalTimeColumn_support E χ t l))
      ((heatNormalTimeColumn_support E χ t l).trans hs) v
    exact hpair.trans (congrArg ((normalizedChartFactor g).toReal * ·)
      (Finset.sum_congr rfl fun k _ => integral_congr_ae (Eventually.of_forall fun x =>
        congrArg (· * f k x) (heatNormalTimeColumn_component E χ t ht l k x))))
  simp only [Finset.sum_apply] at hd
  rw [← hfun, ← hval] at hd
  exact hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! The signed Hessian of the actual first heat amplitude at the center.
Only the curvature-square contribution survives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatWeightedRadialAverage_second_of_vanishing_jet
    (m : ℕ) (U F Q : FourSpace → ℝ) (hU : ContDiff ℝ 2 U) (hF : ContDiff ℝ 2 F)
    (hU0 : ∀ x, U x ≠ 0) (hU1 : U 0 = 1)
    (hQ : (fun x => F x / U x) =ᶠ[𝓝 0] Q)
    (hQ0 : Q 0 = 0) (hQ1 : ∀ i, partialDeriv Q i 0 = 0) (i j : Fin 4) :
    partialDeriv (partialDeriv (fourHeatWeightedRadialAverage m U F) i) j 0 =
      partialDeriv (partialDeriv Q i) j 0 / (m + 3 : ℝ) := by
  have hv : F 0 / U 0 = Q 0 := hQ.self_of_nhds
  rw [fourHeatWeightedRadialAverage_second_zero m U F hU hF hU0,
    hv, hQ0, fourHeat_partial_germ hQ j, fourHeat_partial_germ hQ i,
    hQ1 j, hQ1 i, heat_partial_second_germ hQ i j, hU1]
  simp only [zero_div, mul_zero, zero_add, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A single genuine normal chart and compact cutoff for the time-dependent
parametrix. Its existence simultaneously enforces the domain and residual bounds. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.normalized_initial (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (l : Fin 6) (v : SmoothL2TwoForm o) :
    Filter.Tendsto (fun t => inner ℝ (P.normalizedColumn E t l) (smoothTwoFormToL2 v))
      (nhdsWithin 0 (Ioi 0)) (nhds (twoFormFrameValue o (v : smoothTwoForms o).val e l)) :=
  heatNormalizedParametrixColumn_initial E he P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius P.cutoff (P.cutoff_regular.of_le (by norm_num))
    P.cutoff_compact P.cutoff_support P.cutoff_zero l v

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

theorem heatFamilySignedFirst_regular (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) : ContDiff ℝ 2 (heatFamilySignedFirst E χ) := by
  have hA : ContDiff ℝ 2 (fun z => (twoFormHodgeMatrix * E.amplitude 1 z).trace) :=
    heatSignedTraceLinear.toContinuousLinearMap.contDiff.comp
      (contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
        (E.amplitude_regular 1 (by omega) i j).of_le (by norm_num))))
  exact (((hχ.comp contDiff_fst).pow 2).div (E.U_regular.of_le (by norm_num))
    (fun z => (E.U_pos z).ne')).mul hA

end
end PositiveEinsteinFour.Geometry
end


section

/-! A uniform normal-frame amplitude bound gives an actual global L2
bound. The moving-frame tensor norm is computed using its orthogonality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance instCompactSpaceFrameBundle_28_re876e2_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
theorem heatNormalAmplitudeL2_norm_le
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x, ‖a x‖ ≤ B) :
    ‖heatNormalAmplitudeL2 D C hCt hP hD a ha hc hs‖ ≤ 2 * B := by
  apply (twoFormFromContinuousTensor_norm_le _).trans
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro f
  by_cases hf : f.base ∈ C.target
  · have heq := heatNormalAmplitudeTensor_norm_sq C hE hCt hP hD a ha hc hs f hf
    have hba := hb (C.symm f.base)
    nlinarith [norm_nonneg (a (C.symm f.base)),
      norm_nonneg (heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs f)]
  · have hz : heatNormalAmplitudeTensor D C hCt hP hD a ha hc hs f = 0 := by
      change WithLp.toLp 2 (heatNormalFrameTensorLift g c C (heatNormalCoordinateTensor D a) f) = _
      simp only [heatNormalFrameTensorLift, ite_eq_right hf]
      rfl
    rw [hz, norm_zero]
    positivity

end
end PositiveEinsteinFour.Geometry
end


section

/-! One actual normal chart and compact scalar cutoff. All functions have
the four derivatives required by the finite Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

variable {D : HeatNormalFrameData g o c e}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

def HeatScalarChartData.laplacianColumn (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) :=
  scalarFiniteLaplacianL2 g (P.function t) (P.function_regular t)

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

theorem heatFamilySignedTail_continuous (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilySignedTail E χ z.1 z.2) := by
  have hU := E.U_regular.continuous.comp
    (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have hS (m : ℕ) (hm : m ≤ 3) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      (twoFormHodgeMatrix * E.amplitude m z.2).trace) := by
    have h := heatSignedTraceLinear.toContinuousLinearMap.continuous.comp
      (continuous_pi (fun i => continuous_pi (fun j => (E.amplitude_regular m hm i j).continuous)))
    exact h.comp continuous_snd
  have hG (m n : ℕ) (hm : m ≤ 3) (hn : n ≤ 3) : Continuous (fun z : ℝ × HeatRadialFrameSpace =>
      heatSignedGram (E.amplitude m z.2) (E.amplitude n z.2)) := by
    simp only [heatSignedGram, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    apply continuous_finsetSum
    intro i _
    apply continuous_finsetSum
    intro j _
    apply continuous_const.mul
    apply continuous_finsetSum
    intro k _
    exact ((E.amplitude_regular m hm k j).continuous.comp continuous_snd).mul
      ((E.amplitude_regular n hn k i).continuous.comp continuous_snd)
  have hJ := (hU.pow 2).inv₀ (fun z => pow_ne_zero 2 (E.U_pos z.2).ne')
  have htwo : Continuous (fun _ : ℝ × HeatRadialFrameSpace => (2 : ℝ)) := continuous_const
  have h0 := ((htwo.mul hU).mul (hS 2 (by omega))).add (hG 1 1 (by omega) (by omega))
  have h1 := ((htwo.mul hU).mul (hS 3 (by omega))).add (htwo.mul (hG 1 2 (by omega) (by omega)))
  have h2 := (htwo.mul (hG 1 3 (by omega) (by omega))).add (hG 2 2 (by omega) (by omega))
  exact (hJ.mul ((hχ.comp (continuous_fst.comp continuous_snd)).pow 2)).mul
    ((((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul h2)).add
      ((continuous_fst.pow 3).mul (htwo.mul (hG 2 3 (by omega) (by omega))))).add
        ((continuous_fst.pow 4).mul (hG 3 3 (by omega) (by omega))))

theorem heatFamilySignedTail_bound (E : HeatFamilySmoothCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      ‖heatFamilySignedTail E χ t (x, q)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image
    (heatFamilySignedTail_continuous E χ hχ).norm.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro q hq t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hB ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
  · simp only [heatFamilySignedTail, image_eq_zero_of_notMem_tsupport hx,
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, norm_zero]
    exact le_max_right _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual global residual retains the local cancellation and has
an L2 bound of order t for the constructed chart and cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.timeColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalGlobalTimeColumn E P.chart P.in_chart P.point_regular P.inside_radius
    P.cutoff (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact P.cutoff_support t l

def HeatNormalParametrixData.residual (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatNormalAmplitudeL2 D P.chart P.in_chart P.point_regular P.inside_radius
    (heatNormalResidualColumn E P.cutoff t l)
    (heatNormalResidualColumn_regular E P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalResidualColumn_support E P.cutoff t l))
    ((heatNormalResidualColumn_support E P.cutoff t l).trans P.cutoff_support)

theorem HeatNormalParametrixData.residual_norm_le (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (ht : 0 < t) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ x k l, |deriv (fun s => heatNormalCutoffParametrix E P.cutoff s x k l) t +
      fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
        (fun y q => heatNormalCutoffParametrix E P.cutoff t y q l) x k| ≤ B * t)
    (l : Fin 6) : ‖P.residual E t l‖ ≤ (6 * B) * t := by
  have hn := heatNormalAmplitudeL2_norm_le P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius (heatNormalResidualColumn E P.cutoff t l)
    (heatNormalResidualColumn_regular E P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _) (heatNormalResidualColumn_support E P.cutoff t l))
    ((heatNormalResidualColumn_support E P.cutoff t l).trans P.cutoff_support)
    (3 * (B * t)) (by positivity) (heatNormalResidualColumn_bound E P.cutoff t ht B hB h l)
  exact hn.trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global scalar parametrix has exact normal-coordinate pairings,
including the explicit factor from the normalized geometric volume. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarGlobal_probability
theorem HeatScalarChartData.column_initial (P : HeatScalarChartData D) (f : C(M, ℝ)) :
    Tendsto (fun t => inner ℝ (P.column t) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f))
      (𝓝[Ioi 0] 0) (𝓝 ((normalizedChartFactor g).toReal * f e.base)) := by
  let F := fun x => frameExponentialJacobian g o e x * f (P.chart x)
  have hF : ContinuousOn F P.chart.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      (f.continuous.comp_continuousOn P.chart.continuousOn)
  have hχF := heat_continuous_mul_of_tsupport_subset P.cutoff_regular.continuous
    P.chart.open_source hF P.cutoff_support
  have h := (P.extension.scalarCutoff_initial P.cutoff F hχF P.cutoff_compact
    P.cutoff_zero).const_mul (normalizedChartFactor g).toReal
  have hz : F 0 = f e.base := by
    dsimp only [F]
    rw [frameExponentialJacobian_zero, P.chart_zero, one_mul]
  rw [hz] at h
  exact h.congr' (Eventually.of_forall fun t => (P.column_pairing t f).symm)

theorem HeatScalarChartData.normalizedColumn_initial (P : HeatScalarChartData D)
    (f : C(M, ℝ)) :
    Tendsto (fun t => inner ℝ (P.normalizedColumn t)
      (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f)) (𝓝[Ioi 0] 0) (𝓝 (f e.base)) := by
  have h := (P.column_initial f).const_mul ((normalizedChartFactor g).toReal)⁻¹
  have hn : (normalizedChartFactor g).toReal ≠ 0 := (normalizedChartFactor_toReal_pos g).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hn, one_mul] at h
  simpa only [HeatScalarChartData.normalizedColumn, real_inner_smul_left] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The cutoff scalar column has exactly the geometric Laplacian prescribed
by the normal-coordinate operator on the actual chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.scalar_laplacian_local (P : HeatScalarChartData D)
    (f : M → ℝ) (hf : ContMDiff I4 𝓘(ℝ, ℝ) 4 f) (x : FourSpace)
    (hx : x ∈ P.chart.source) (hd : 0 < (heatNormalMetric g o e x).det) :
    fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
      (fun y => f (P.chart y)) x = -scalarLaplacianBase g f (P.chart x) := by
  let φ := fun z => f ((chartAt FourSpace c).symm z)
  have htarget := D.in_chart x (P.inside_radius hx)
  have hφ : ContDiffAt ℝ 2 φ (D.point x).1 :=
    ((hf.contMDiffAt.comp _ (contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas c) htarget)).contDiffAt).of_le (by norm_num)
  have hpoint (y : FourSpace) (hy : y ∈ P.chart.source) :
      (D.point y).1 = chartAt FourSpace c (P.chart y) :=
    (D.exponential y (P.inside_radius hy)).trans
      (congrArg (chartAt FourSpace c) (P.exponential hy).symm)
  have hcomp : (fun y => φ (D.point y).1) =ᶠ[𝓝 x] (fun y => f (P.chart y)) := by
    filter_upwards [P.chart.open_source.mem_nhds hx] with y hy
    dsimp only [φ]
    rw [hpoint y hy, (chartAt FourSpace c).left_inv (P.in_chart (P.chart.map_source hy))]
  have hs : frameExponential g o e x ∈ (chartAt FourSpace c).source := by
    rw [← P.exponential hx]
    exact P.in_chart (P.chart.map_source hx)
  calc
    _ = fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
        (fun y => φ (D.point y).1) x := (fourHeatLocalOperator_germ _ _ _ hcomp).symm
    _ = -scalarChartOperator g c φ (D.point x).1 := D.scalar_operator_pullback x
      (P.inside_radius hx) (P.point_regular.contDiffAt (P.chart.open_source.mem_nhds hx) |>.of_le
        (by norm_num)) hs hd φ hφ
    _ = -scalarLaplacianBase g f ((chartAt FourSpace c).symm (D.point x).1) :=
      congrArg Neg.neg (scalar_finite_chart_laplacian g hf c ⟨_, htarget⟩).symm
    _ = _ := by
      rw [hpoint x hx, (chartAt FourSpace c).left_inv (P.in_chart (P.chart.map_source hx))]

theorem HeatScalarChartData.column_laplacian_local (P : HeatScalarChartData D)
    (t : ℝ) (x : FourSpace) (hx : x ∈ P.chart.source)
    (hd : 0 < (heatNormalMetric g o e x).det) :
    fourHeatLocalOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) 0
      (P.extension.scalarCutoff P.cutoff t) x =
        -scalarLaplacianBase g (P.function t) (P.chart x) := by
  have he : (fun y => P.function t (P.chart y)) =ᶠ[𝓝 x]
      P.extension.scalarCutoff P.cutoff t := by
    filter_upwards [P.chart.open_source.mem_nhds hx] with y hy
    exact heatNormalScalarLift_source P.chart _ hy
  rw [← fourHeatLocalOperator_germ _ _ _ he]
  exact P.scalar_laplacian_local (P.function t) (P.function_regular t) x hx hd

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

theorem HeatNormalParametrixData.column_growth (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (l : Fin 6) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.column E t l‖ ≤ C / t := by
  obtain ⟨B, hB, hb⟩ := heatNormalCutoffColumn_square_integral_bound E P.cutoff
    (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact l
  let K := 2 * (normalizedChartFactor g).toReal * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K + 1, by positivity, ?_⟩
  intro t ht
  have hn := heatNormalAmplitudeL2_norm_sq_le_integral P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius (heatNormalCutoffColumn E P.cutoff t l)
    (heatNormalCutoffColumn_regular E P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support E P.cutoff t l))
    ((heatNormalCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)
  have hn' : ‖P.column E t l‖ ^ 2 ≤ K / t ^ 2 := by
    exact hn.trans ((mul_le_mul_of_nonneg_left (hb t ht) (by positivity)).trans_eq (by dsimp [K]; ring))
  have hs : (‖P.column E t l‖ * t) ^ 2 ≤ K := by
    calc
      _ = ‖P.column E t l‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (K / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      _ = K := by field_simp [ht.1.ne']
  apply (le_div_iff₀ ht.1).mpr
  nlinarith [sq_nonneg K, norm_nonneg (P.column E t l)]

theorem HeatNormalParametrixData.normalizedColumn_growth (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (l : Fin 6) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.normalizedColumn E t l‖ ≤ C / t := by
  obtain ⟨C, hC, hc⟩ := P.column_growth E l
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * C, by positivity, ?_⟩
  intro t ht
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.column E t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hc t ht) (norm_nonneg _)).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual time derivative of the global scalar parametrix is a
compact C4 function, represented in the same scalar L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarTime_probability
theorem HeatScalarChartData.column_weak_deriv (P : HeatScalarChartData D)
    (t : ℝ) (ht : 0 < t) (f : C(M, ℝ)) :
    HasDerivAt (fun s => inner ℝ (P.column s) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f))
      (inner ℝ (P.timeColumn t) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f)) t := by
  let F := fun x => frameExponentialJacobian g o e x * f (P.chart x)
  have hF : ContinuousOn F P.chart.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      (f.continuous.comp_continuousOn P.chart.continuousOn)
  have hχF := heat_continuous_mul_of_tsupport_subset P.cutoff_regular.continuous
    P.chart.open_source hF P.cutoff_support
  have h := (P.extension.scalarCutoff_pairing_deriv P.cutoff F hχF P.cutoff_compact
    t ht).const_mul (normalizedChartFactor g).toReal
  have hval : inner ℝ (P.timeColumn t) (ContinuousMap.toLp 2 (normalizedVolume g) ℝ f) =
      (normalizedChartFactor g).toReal *
        ∫ x, deriv (fun s => P.extension.scalarCutoff P.cutoff s x) t * F x := by
    rw [P.timeColumn_pairing]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => congrArg (· * F x) (P.timeAmplitude_eq t ht x)
  rw [← hval] at h
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun s => P.column_pairing s f)

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

/-! Each actual smooth Hodge eigenmode satisfies the scalar forced heat
equation for the constructed normal parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.normalizedResidual (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  ((normalizedChartFactor g).toReal)⁻¹ • P.residual E t l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact scalar parametrix satisfies the forced heat ODE
in every eigenmode. Its forcing is its genuine time-minus-Laplacian residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarEvolution_probability
def HeatScalarChartData.residual (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) := P.timeColumn t - P.laplacianColumn t

def HeatScalarChartData.normalizedResidual (P : HeatScalarChartData D) (t : ℝ) :
    Lp ℝ 2 (normalizedVolume g) := ((normalizedChartFactor g).toReal)⁻¹ • P.residual t

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal columns have a common L2 growth constant
for every initial frame in a compact coordinate set. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set MeasureTheory Filter Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformColumn_growth (E : HeatFamilySmoothCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ C ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonNormalMember g o c E r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l,
      ‖(N.parametrixData hr).normalizedColumn N.extension t l‖ ≤ C / t := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hχs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  obtain ⟨B, hB, hb⟩ := heatUniformPolynomial_weight_bound (g := g) (o := o) (c := c) E r χ
    (heatNormalChartBump r hr).continuous (heatNormalChartBump r hr).hasCompactSupport hχs K hK
  let A := B / (64 * Real.pi ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C := 2 * (normalizedChartFactor g).toReal * A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * (C + 1), by positivity, ?_⟩
  intro e N hq t ht l
  let P := N.parametrixData hr
  have hcut : P.cutoff = χ := rfl
  have hpt (x : FourSpace) : frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn N.extension χ t l x‖ ^ 2 ≤ B * fourHeatGaussian t x ^ 2 := by
    rw [heatNormalCutoffColumn_gaussian, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    calc
      _ = (frameExponentialJacobian g o e x * ‖heatNormalPolynomialColumn N.extension χ t l x‖ ^ 2) *
          fourHeatGaussian t x ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hb e N hq t ⟨ht.1.le, ht.2⟩ x l) (sq_nonneg _)
  have hi : Integrable (fun x : FourSpace => B * fourHeatGaussian t x ^ 2) :=
    (fourHeatGaussian_square_integrable t ht.1).const_mul B
  have hm : Continuous (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn N.extension χ t l x‖ ^ 2) :=
    (frameExponentialJacobian_continuous g o e).mul
      ((heatNormalCutoffColumn_regular N.extension χ
        (heatNormalChartBump r hr).contDiff t l).continuous.norm.pow 2)
  have hfi : Integrable (fun x => frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn N.extension χ t l x‖ ^ 2) :=
    hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (frameExponentialJacobian_nonneg g o e x) (sq_nonneg _))]
      exact hpt x)
  have hint : (∫ x, frameExponentialJacobian g o e x *
      ‖heatNormalCutoffColumn N.extension χ t l x‖ ^ 2) ≤ A / t ^ 2 := by
    calc
      _ ≤ ∫ x : FourSpace, B * fourHeatGaussian t x ^ 2 := integral_mono hfi hi hpt
      _ = _ := by rw [integral_const_mul, fourHeatGaussian_square_mass t ht.1]; dsimp [A]; ring
  have hn := heatNormalAmplitudeL2_norm_sq_le_integral P.chart P.exponential P.in_chart
    P.point_regular P.inside_radius (heatNormalCutoffColumn N.extension P.cutoff t l)
    (heatNormalCutoffColumn_regular N.extension P.cutoff (P.cutoff_regular.of_le (by norm_num)) t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalCutoffColumn_support N.extension P.cutoff t l))
    ((heatNormalCutoffColumn_support N.extension P.cutoff t l).trans P.cutoff_support)
  have hn' : ‖P.column N.extension t l‖ ^ 2 ≤ C / t ^ 2 := by
    have hint' : (∫ x, frameExponentialJacobian g o e x *
        ‖heatNormalCutoffColumn N.extension P.cutoff t l x‖ ^ 2) ≤ A / t ^ 2 := by
      simpa only [hcut] using hint
    exact hn.trans ((mul_le_mul_of_nonneg_left hint' (by positivity)).trans_eq (by dsimp [C]; ring))
  have hs : (‖P.column N.extension t l‖ * t) ^ 2 ≤ C := by
    calc
      _ = ‖P.column N.extension t l‖ ^ 2 * t ^ 2 := by ring
      _ ≤ (C / t ^ 2) * t ^ 2 := mul_le_mul_of_nonneg_right hn' (sq_nonneg t)
      _ = C := by field_simp [ht.1.ne']
  have hcol : ‖P.column N.extension t l‖ ≤ (C + 1) / t := by
    apply (le_div_iff₀ ht.1).mpr
    nlinarith [sq_nonneg C, norm_nonneg (P.column N.extension t l)]
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.column N.extension t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left hcol (norm_nonneg _)).trans_eq (by ring)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time L2 continuity of the actual normal parametrix and residual. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.residual_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (l : Fin 6) :
    ContinuousOn (fun t => P.residual E t l) (Ioi 0) := by
  apply heatNormalAmplitudeL2_continuous_family P.chart P.in_chart P.point_regular P.inside_radius
    (fun t => heatNormalResidualColumn E P.cutoff t l)
    (fun t => heatNormalResidualColumn_regular E P.cutoff P.cutoff_regular t l)
    (fun t => P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalResidualColumn_support E P.cutoff t l))
    (fun t => (heatNormalResidualColumn_support E P.cutoff t l).trans P.cutoff_support)
    ?_ (tsupport P.cutoff) P.cutoff_compact P.cutoff_support
    (fun t _ => heatNormalResidualColumn_support E P.cutoff t l)
  exact (heatNormalResidualColumn_joint_continuousOn E P.cutoff
    (P.cutoff_regular.of_le (by norm_num)) l).mono (prod_mono Subset.rfl (subset_univ _))

theorem HeatNormalParametrixData.normalizedResidual_continuous (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (l : Fin 6) :
    ContinuousOn (fun t => P.normalizedResidual E t l) (Ioi 0) := by
  exact (P.residual_continuous E l).const_smul ((normalizedChartFactor g).toReal)⁻¹

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar transport equation and its actual compact cutoff have a
uniform linearly vanishing residual, including the cutoff annulus. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter Metric
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.residualAmplitude_bound (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hχ : ∀ x, |P.cutoff x| ≤ 1)
    (r : ℝ) (hr : 0 < r) (hinner : ∀ x ∈ ball 0 r, P.cutoff x = 1)
    (hres : ∀ x ∈ tsupport P.cutoff, ∀ t > (0 : ℝ),
      deriv (fun v => P.extension.scalarParametrix v x) t +
        fourHeatLocalOperator (P.extension.a x) (P.extension.b x) 0
          (P.extension.scalarParametrix t) x =
        fourHeatGaussian t x * t ^ 3 * fourHeatLocalOperator (P.extension.a x)
          (P.extension.b x) 0 (P.extension.scalarAmplitude 3) x) :
    ∃ B ≥ (0 : ℝ), ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x, |P.residualAmplitude t x| ≤ B * t := by
  let E := P.extension
  let u : Fin 4 → FourSpace → Fin 6 → ℝ := fun m y _ => E.scalarAmplitude m y
  have hu (m : Fin 4) (q : Fin 6) : ContDiff ℝ 2 (fun y => u m y q) :=
    (E.scalarAmplitude_regular m (by omega)).of_le (by norm_num)
  obtain ⟨B₁, hB₁, hb₁⟩ := fourHeatScaledCommutator_gaussian_bound E.a E.b
    (fun _ => 0) P.cutoff u
    (fun i j => (E.a_regular i j).continuous)
    (fun i => (E.b_regular i).continuous) (fun _ _ _ => continuous_const)
    (P.cutoff_regular.of_le (by norm_num)) P.cutoff_compact hu r hr hinner
  let F := fun x => fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarAmplitude 3) x
  have hF : Continuous F :=
    (fourHeatLocalOperator_contDiff 2 E.a E.b (fun _ => 0) (E.scalarAmplitude 3)
      (fun i j => (E.a_regular i j).of_le (by norm_num))
      (fun i => (E.b_regular i).of_le (by norm_num)) contDiff_const
      (E.scalarAmplitude_regular 3 (by omega))).continuous
  obtain ⟨A, hA⟩ := P.cutoff_compact.bddAbove_image hF.abs.continuousOn
  let B₀ := max A 0 / (16 * Real.pi ^ 2)
  have hB₀ : 0 ≤ B₀ := by positivity
  refine ⟨B₀ + B₁, add_nonneg hB₀ hB₁, ?_⟩
  intro t ht x
  by_cases hx : x ∈ tsupport P.cutoff
  · have hsym (i j : Fin 4) : E.a x i j = E.a x j i := by
      rw [ha x hx]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    have hQ : |deriv (fun v => E.scalarParametrix v x) t +
        fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x| ≤ B₀ * t := by
      rw [hres x hx t ht.1, abs_mul, abs_mul,
        abs_of_pos (fourHeatGaussian_pos t ht.1 x), abs_of_pos (pow_pos ht.1 3)]
      have hFx : |F x| ≤ max A 0 := (hA (mem_image_of_mem _ hx)).trans (le_max_left _ _)
      calc
        _ ≤ (fourHeatGaussian t x * t ^ 3) * max A 0 :=
          mul_le_mul_of_nonneg_left hFx
            (mul_nonneg (fourHeatGaussian_pos t ht.1 x).le (pow_nonneg ht.1.le 3))
        _ ≤ (fourHeatGaussian t 0 * t ^ 3) * max A 0 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (fourHeatGaussian_le_diagonal t ht.1 x)
              (pow_nonneg ht.1.le 3)) (le_max_right _ _)
        _ = B₀ * t := by
          have hg := fourHeatGaussian_diagonal_power 1 t ht.1
          norm_num only [Nat.reduceAdd, pow_one] at hg
          dsimp only [B₀]
          calc
            _ = max A 0 * (t ^ 3 * fourHeatGaussian t 0) := by ring
            _ = _ := by rw [hg]; ring
    have hcut := fourHeatLocalOperator_cutoff (E.a x) (E.b x) P.cutoff
      (E.scalarParametrix t) x hsym (P.cutoff_regular.contDiffAt.of_le (by norm_num))
      ((E.scalarParametrix_regular t).contDiffAt.of_le (by norm_num))
    have hscaled := fourHeatScaledCommutator_identity E.a E.b (fun _ => 0)
      P.cutoff u hu t ht.1 x 0
    have hz (i : Fin 4) (q : Fin 6) : (0 : Fin 4 → HeatMat6) i 0 q = 0 := rfl
    simp only [fourHeatBundlePolynomial, u, hz, zero_mul,
      Finset.sum_const_zero, add_zero] at hscaled
    have hdt : deriv (fun v => E.scalarParametrix v x) t =
        fourHeatGaussianPolynomialTime (fun m => E.scalarAmplitude m) t x :=
      (fourHeatGaussianPolynomial_hasDerivAt
        (fun m => E.scalarAmplitude m) t ht.1 x).deriv
    have hid : P.residualAmplitude t x =
        P.cutoff x * (deriv (fun v => E.scalarParametrix v x) t +
          fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x) +
        (fourHeatGaussian t x / t) *
          fourHeatScaledCommutator E.a E.b (fun _ => 0) P.cutoff u t x 0 := by
      change P.cutoff x * fourHeatGaussianPolynomialTime
        (fun m => E.scalarAmplitude m) t x +
        fourHeatLocalOperator (E.a x) (E.b x) 0
          (fun y => P.cutoff y * E.scalarParametrix t y) x = _
      rw [hcut, hdt]
      change fourHeatLocalOperator (E.a x) (E.b x) 0 P.cutoff x * E.scalarParametrix t x -
        2 * (∑ i, ∑ j, E.a x i j * partialDeriv P.cutoff i x *
          partialDeriv (E.scalarParametrix t) j x) = _ at hscaled
      linarith [hscaled]
    rw [hid]
    calc
      _ ≤ |P.cutoff x * (deriv (fun v => E.scalarParametrix v x) t +
          fourHeatLocalOperator (E.a x) (E.b x) 0 (E.scalarParametrix t) x)| +
          |(fourHeatGaussian t x / t) *
            fourHeatScaledCommutator E.a E.b (fun _ => 0) P.cutoff u t x 0| := abs_add_le _ _
      _ ≤ B₀ * t + B₁ * t := by
        apply add_le_add _ (hb₁ t ht x 0)
        rw [abs_mul]
        exact (mul_le_mul (hχ x) hQ (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (P.residualAmplitude_support t h)),
      abs_zero]
    exact mul_nonneg (add_nonneg hB₀ hB₁) ht.1.le

end
end PositiveEinsteinFour.Geometry
end


section

/-! The forcing in the spectral scalar ODE is the actual compactly
supported local parametrix residual, with no domain or operator premise. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.residualFunction_eq (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (t : ℝ) (y : M) :
    P.residualFunction t y = P.timeFunction t y - scalarLaplacianBase g (P.function t) y := by
  by_cases hy : y ∈ P.chart '' tsupport P.cutoff
  · obtain ⟨x, hx, rfl⟩ := hy
    have hs := P.cutoff_support hx
    have hL := P.column_laplacian_local t x hs (hd x hx)
    change heatNormalScalarLift P.chart (P.residualAmplitude t) (P.chart x) =
      heatNormalScalarLift P.chart (P.timeAmplitude t) (P.chart x) - _
    rw [heatNormalScalarLift_source P.chart _ hs, heatNormalScalarLift_source P.chart _ hs]
    change P.timeAmplitude t x + fourHeatLocalOperator (P.extension.a x) (P.extension.b x) 0
      (P.extension.scalarCutoff P.cutoff t) x = _
    rw [ha x hx, hb x hx, hL]
    ring
  · have hR : P.residualFunction t y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (P.residualFunction_support t h))
    have hT : P.timeFunction t y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (P.timeFunction_support t h))
    have hL : scalarLaplacianBase g (P.function t) y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy
        (P.function_support t (scalarLaplacianBase_tsupport g (P.function t) h)))
    rw [hR, hT, hL, sub_self]

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarResidual_probability
theorem HeatScalarChartData.residual_realization (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det) (t : ℝ) :
    P.residual t = ContinuousMap.toLp 2 (normalizedVolume g) ℝ
      ⟨P.residualFunction t, P.residualFunction_continuous t⟩ := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (P.timeColumn t) (P.laplacianColumn t),
    scalarFiniteValueL2_coe g (P.timeFunction t) (P.timeFunction_regular t),
    scalarFiniteLaplacianL2_coe g (P.function t) (P.function_regular t),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (⟨P.residualFunction t, P.residualFunction_continuous t⟩ : C(M, ℝ))] with y hsub hT hL hR
  change (P.timeColumn t - P.laplacianColumn t) y = _
  rw [hsub]
  change scalarFiniteValueL2 g (P.timeFunction t) (P.timeFunction_regular t) y -
    scalarFiniteLaplacianL2 g (P.function t) (P.function_regular t) y = _
  rw [hT, hL, hR]
  exact (P.residualFunction_eq ha hb hd t y).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive-time continuity of the actual scalar cutoff and its residual
in the global scalar L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatScalarChartData.residualAmplitude_joint_continuous (P : HeatScalarChartData D) :
    ContinuousOn (fun z : ℝ × FourSpace => P.residualAmplitude z.1 z.2) (Ioi 0 ×ˢ univ) := by
  have ht : ContinuousOn (fun z : ℝ × FourSpace => P.timeAmplitude z.1 z.2)
      (Ioi 0 ×ˢ univ) :=
    (P.cutoff_regular.continuous.comp continuous_snd).continuousOn.mul
      (fourHeatGaussianPolynomialTime_continuousOn _
        (fun m => (P.extension.scalarAmplitude_regular m (by omega)).continuous))
  apply ht.add
  intro z hz
  have h := fourHeatBundleOperator_joint_continuousAt P.extension.a P.extension.b
    (fun _ => 0) (fun _ => 0)
    (fun w _ => P.extension.scalarCutoff P.cutoff w.1 w.2) z
    (fun i j => (P.extension.a_regular i j).continuous.continuousAt)
    (fun i => (P.extension.b_regular i).continuous.continuousAt)
    (fun _ _ _ => continuousAt_const) (fun _ _ => continuousAt_const)
    (fun _ => P.cutoff_joint_regular z hz.1) 0
  have hB (i : Fin 4) (q : Fin 6) : (0 : Fin 4 → HeatMat6) i 0 q = 0 := rfl
  have hC (q : Fin 6) : (0 : HeatMat6) 0 q = 0 := rfl
  simpa only [fourHeatBundleOperator, fourHeatBundleFirst, fourHeatBundleZero,
    hB, hC, zero_mul, Finset.sum_const_zero, add_zero] using h.continuousWithinAt

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarContinuity_probability
theorem HeatScalarChartData.residual_continuous (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det) :
    ContinuousOn P.residual (Ioi 0) := by
  have hF : ContinuousOn (fun z : ℝ × M => P.residualFunction z.1 z.2) (Ioi 0 ×ˢ univ) :=
    heatNormalScalarLift_joint_continuous P.chart P.residualAmplitude
      (P.residualAmplitude_joint_continuous.mono (prod_mono Subset.rfl (subset_univ _)))
      (tsupport P.cutoff) P.cutoff_compact P.cutoff_support
      (fun t _ => P.residualAmplitude_support t)
  have hC : ContinuousOn (fun t =>
      (⟨P.residualFunction t, P.residualFunction_continuous t⟩ : C(M, ℝ))) (Ioi 0) :=
    ContinuousMap.continuousOn_of_continuousOn_uncurry _ hF
  exact ((ContinuousMap.toLp 2 (normalizedVolume g) ℝ).continuous.comp_continuousOn hC).congr
    (fun t _ => P.residual_realization ha hb hd t)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform bounds for the remaining coefficients of the common Euler polynomial. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatFamilyEulerTail_continuous (F : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : ℝ × HeatRadialFrameSpace => heatFamilyEulerTail F χ z.1 z.2) := by
  have hU := F.base.U_regular.continuous.comp
    (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have hS (m : ℕ) (hm : m ≤ 3) :=
    (heatEulerTrace_continuous.comp (F.eulerAmplitude_continuous m hm)).comp
      (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have hG (m n : ℕ) (hm : m ≤ 3) (hn : n ≤ 3) :=
    (heatEulerGram_continuous.comp ((F.eulerAmplitude_continuous m hm).prodMk
      (F.eulerAmplitude_continuous n hn))).comp
        (continuous_snd : Continuous (fun z : ℝ × HeatRadialFrameSpace => z.2))
  have hJ := (hU.pow 2).inv₀ (fun z => pow_ne_zero 2 (F.base.U_pos z.2).ne')
  have htwo : Continuous (fun _ : ℝ × HeatRadialFrameSpace => (2 : ℝ)) := continuous_const
  have h0 := ((htwo.mul hU).mul (hS 2 (by omega))).add (hG 1 1 (by omega) (by omega))
  have h1 := ((htwo.mul hU).mul (hS 3 (by omega))).add (htwo.mul (hG 1 2 (by omega) (by omega)))
  have h2 := (htwo.mul (hG 1 3 (by omega) (by omega))).add (hG 2 2 (by omega) (by omega))
  exact (hJ.mul ((hχ.comp (continuous_fst.comp continuous_snd)).pow 2)).mul
    ((((h0.add (continuous_fst.mul h1)).add ((continuous_fst.pow 2).mul h2)).add
      ((continuous_fst.pow 3).mul (htwo.mul (hG 2 3 (by omega) (by omega))))).add
        ((continuous_fst.pow 4).mul (hG 3 3 (by omega) (by omega))))

theorem heatFamilyEulerTail_bound (F : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) :
    ∃ B ≥ (0 : ℝ), ∀ q ∈ K, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x,
      ‖heatFamilyEulerTail F χ t (x, q)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (hc.prod hK)).bddAbove_image
    (heatFamilyEulerTail_continuous F χ hχ).norm.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro q hq t ht x
  by_cases hx : x ∈ tsupport χ
  · exact (hB ⟨(t, (x, q)), ⟨ht, hx, hq⟩, rfl⟩).trans (le_max_left _ _)
  · simp only [heatFamilyEulerTail, image_eq_zero_of_notMem_tsupport hx,
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, norm_zero]
    exact le_max_right _ _

theorem heatFamilyEulerPolynomial_gram (F : HeatFamilyOneCoefficients)
    (χ : FourSpace → ℝ) (t : ℝ) (z : HeatRadialFrameSpace) :
    (F.base.U z ^ 2)⁻¹ * χ z.1 ^ 2 *
      heatEulerGram (F.eulerPolynomial t z) (F.eulerPolynomial t z) =
        2 * t * heatFamilyEulerFirst F χ z + t ^ 2 * heatFamilyEulerTail F χ t z := by
  rw [HeatFamilyOneCoefficients.eulerPolynomial, heatEulerGram_polynomial]
  unfold heatFamilyEulerFirst heatFamilyEulerTail
  field_simp [(F.base.U_pos z).ne']

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized residual has a continuous zero-time extension. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalParametrixData.normalizedResidualZero (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (t : ℝ) (l : Fin 6) : TwoFormL2 o :=
  heatResidualAtZero (fun s => P.normalizedResidual E s l) t

theorem HeatNormalParametrixData.normalizedResidual_bound (P : HeatNormalParametrixData D)
    (E : HeatNormalBundleExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 6) :
    ‖P.normalizedResidual E t l‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t := by
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.residual E t l‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hB t ht l) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem HeatNormalParametrixData.normalizedResidualZero_continuous
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t) (l : Fin 6) :
    ContinuousOn (fun t => P.normalizedResidualZero E t l) (Icc 0 1) :=
  heatResidualAtZero_continuous _ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) 1
    zero_lt_one (P.normalizedResidual_continuous E l)
    (fun t ht => P.normalizedResidual_bound E B hB t ht l)

theorem HeatNormalParametrixData.normalizedResidualZero_eq
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D)
    (t : ℝ) (ht : 0 < t) (l : Fin 6) :
    P.normalizedResidualZero E t l = P.normalizedResidual E t l := by
  unfold normalizedResidualZero heatResidualAtZero
  exact Function.update_of_ne ht.ne' _ _

theorem HeatNormalParametrixData.normalizedResidualZero_bound
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (B : ℝ)
    (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.residual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (l : Fin 6) :
    ‖P.normalizedResidualZero E t l‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t :=
  heatResidualAtZero_norm _ _ 1 (fun s hs => P.normalizedResidual_bound E B hB s hs l) t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar forcing has an O(t) L2 bound and a continuous
zero extension. All local coefficient conditions are realized geometrically. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.scalarGlobalResidual_probability
theorem HeatScalarChartData.residual_norm_le (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (t B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x, |P.residualAmplitude t x| ≤ B) :
    ‖P.residual t‖ ≤ ‖ContinuousMap.toLp (E := ℝ) 2 (normalizedVolume g) ℝ‖ * B := by
  rw [P.residual_realization ha hb hd t]
  apply (ContinuousMap.toLp (E := ℝ) 2 (normalizedVolume g) ℝ).le_opNorm_of_le
  apply (ContinuousMap.norm_le _ hB).mpr
  intro y
  change |heatNormalScalarLift P.chart (P.residualAmplitude t) y| ≤ B
  by_cases hy : y ∈ P.chart.target
  · rw [heatNormalScalarLift_on_target P.chart _ hy]
    exact hbound _
  · simpa only [heatNormalScalarLift, ite_eq_right hy, abs_zero] using hB

def HeatScalarChartData.normalizedResidualZero (P : HeatScalarChartData D) :
    ℝ → Lp ℝ 2 (normalizedVolume g) := heatResidualAtZero P.normalizedResidual

theorem HeatScalarChartData.normalizedResidual_bound (P : HeatScalarChartData D)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) :
    ‖P.normalizedResidual t‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t := by
  change ‖((normalizedChartFactor g).toReal)⁻¹ • P.residual t‖ ≤ _
  rw [norm_smul]
  exact (mul_le_mul_of_nonneg_left (hB t ht) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem HeatScalarChartData.normalizedResidualZero_continuous (P : HeatScalarChartData D)
    (ha : ∀ x ∈ tsupport P.cutoff, P.extension.a x = (heatNormalMetric g o e x)⁻¹)
    (hb : ∀ x ∈ tsupport P.cutoff, P.extension.b x = heatNormalDrift g o e x)
    (hd : ∀ x ∈ tsupport P.cutoff, 0 < (heatNormalMetric g o e x).det)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t) :
    ContinuousOn P.normalizedResidualZero (Icc 0 1) :=
  heatResidualAtZero_continuous _ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) 1
    zero_lt_one ((P.residual_continuous ha hb hd).const_smul ((normalizedChartFactor g).toReal)⁻¹)
    (fun t ht => P.normalizedResidual_bound B hB t ht)

theorem HeatScalarChartData.normalizedResidualZero_eq (P : HeatScalarChartData D)
    (t : ℝ) (ht : 0 < t) : P.normalizedResidualZero t = P.normalizedResidual t := by
  unfold normalizedResidualZero heatResidualAtZero
  exact Function.update_of_ne ht.ne' _ _

theorem HeatScalarChartData.normalizedResidualZero_bound (P : HeatScalarChartData D)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ‖P.residual t‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖P.normalizedResidualZero t‖ ≤ (‖((normalizedChartFactor g).toReal)⁻¹‖ * B) * t :=
  heatResidualAtZero_norm _ _ 1 (fun s hs => P.normalizedResidual_bound B hB s hs) t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! One Gaussian bound for the alternating polynomial of the three actual degrees. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set MeasureTheory Metric
open scoped ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}

theorem heatUniformEulerIntegral_bound (F : HeatFamilyOneCoefficients) (r : ℝ)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 2 χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ ball 0 r) (K : Set CoordinateFrameSpace) (hK : IsCompact K)
    (hRic : RicciThree g) :
    ∃ D ≥ (0 : ℝ), ∀ (e : FrameBundle g) (_N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1,
      ‖∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
        ((F.base.U (x, frameCoordinateState g c e) ^ 2)⁻¹ * χ x ^ 2 *
          heatEulerGram (F.eulerPolynomial t (x, frameCoordinateState g c e))
            (F.eulerPolynomial t (x, frameCoordinateState g c e)))‖ ≤ D := by
  obtain ⟨C, hC, hb⟩ := heatUniformEulerFirst_quadratic (g := g) (o := o) (c := c)
    F r χ hχ hχs K hK hRic
  obtain ⟨B, hB, ht⟩ := heatFamilyEulerTail_bound F χ hχ.continuous hc K hK
  refine ⟨(32 * C + B) / (64 * Real.pi ^ 2), by positivity, ?_⟩
  intro e N hq t htt
  simp_rw [heatFamilyEulerPolynomial_gram]
  apply fourHeat_signed_gaussian_bound _ _ C B t hC hB htt.1 (hb e N hq)
  intro x
  exact ht _ hq t ⟨htt.1.le, htt.2⟩ x

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

theorem heatNormalPolynomialColumn_signed (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) :
    (∑ l, ∑ m, twoFormHodgeMatrix l m *
      inner ℝ (heatNormalPolynomialColumn E χ t l x) (heatNormalPolynomialColumn E χ t m x)) =
      χ x ^ 2 * heatSignedGram (heatNormalMatrixPolynomial E t x) (heatNormalMatrixPolynomial E t x) := by
  simp_rw [heatNormalPolynomialColumn_matrix, real_inner_smul_left, real_inner_smul_right]
  rw [heatSignedGram_columns]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro m _
  ring

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatNormalParametrixData.signedColumn_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalBundleExtension D) (t : ℝ) :
    (∑ l, ∑ m, twoFormHodgeMatrix l m * inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m)) =
      ((normalizedChartFactor g).toReal)⁻¹ * ∫ x : FourSpace, fourHeatGaussian t x ^ 2 *
        (frameExponentialJacobian g o e x * P.cutoff x ^ 2 *
          heatSignedGram (heatNormalMatrixPolynomial E t x) (heatNormalMatrixPolynomial E t x)) := by
  let F := fun l m x => twoFormHodgeMatrix l m * (fourHeatGaussian t x ^ 2 *
    (frameExponentialJacobian g o e x * inner ℝ (heatNormalPolynomialColumn E P.cutoff t l x)
      (heatNormalPolynomialColumn E P.cutoff t m x)))
  have hF (l m : Fin 6) : Integrable (F l m) :=
    (P.polynomial_pair_integrable E t l m).const_mul _
  have he (l m : Fin 6) : twoFormHodgeMatrix l m *
      inner ℝ (P.normalizedColumn E t l) (P.normalizedColumn E t m) =
      ((normalizedChartFactor g).toReal)⁻¹ * ∫ x, F l m x := by
    rw [P.normalizedColumn_gaussian_inner E t l m]
    dsimp only [F]
    rw [integral_const_mul]
    ring
  simp_rw [he]
  simp only [← Finset.mul_sum]
  congr 1
  have hs (l : Fin 6) : (∑ m, ∫ y, F l m y) = ∫ y, ∑ m, F l m y :=
    (integral_finsetSum _ (fun m _ => hF l m)).symm
  simp_rw [hs]
  rw [← integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun m _ => hF l m))]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (∑ l, ∑ m, F l m x) = _
    dsimp only [F]
    calc
      _ = fourHeatGaussian t x ^ 2 * frameExponentialJacobian g o e x *
          (∑ l, ∑ m, twoFormHodgeMatrix l m *
            inner ℝ (heatNormalPolynomialColumn E P.cutoff t l x)
              (heatNormalPolynomialColumn E P.cutoff t m x)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro m _
        ring
      _ = _ := by rw [heatNormalPolynomialColumn_signed]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normalized column supertrace is the common Euler Gaussian integral. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem heatUniformEulerColumnTrace_bound (F : HeatFamilyOneCoefficients) (r : ℝ) (hr : 0 < r)
    (K : Set CoordinateFrameSpace) (hK : IsCompact K) (hRic : RicciThree g) :
    ∃ B ≥ (0 : ℝ), ∀ (e : FrameBundle g) (N : HeatCommonEulerMember g o c F r e),
      frameCoordinateState g c e ∈ K → ∀ t ∈ Ioc (0 : ℝ) 1, ‖N.eulerColumnTrace hr t‖ ≤ B := by
  let χ : FourSpace → ℝ := heatNormalChartBump r hr
  have hs : tsupport χ ⊆ ball (0 : FourSpace) r := by
    rw [(heatNormalChartBump r hr).tsupport_eq]
    exact closedBall_subset_ball (by change r / 2 < r; linarith)
  obtain ⟨B, hB, hb⟩ := heatUniformEulerIntegral_bound (g := g) (o := o) (c := c) F r χ
    (heatNormalChartBump r hr).contDiff (heatNormalChartBump r hr).hasCompactSupport hs K hK hRic
  refine ⟨‖((normalizedChartFactor g).toReal)⁻¹‖ * B, by positivity, ?_⟩
  intro e N hq t ht
  rw [N.eulerColumnTrace_family hr t, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb e N hq t ht) (norm_nonneg _)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


