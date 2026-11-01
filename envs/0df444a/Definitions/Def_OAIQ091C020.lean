-- Prove2me | Definitions.Def_OAIQ091C020
-- name    : OAIQ091C020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:50:18.78015+00:00
-- url     : https://prove2.me/theorems/fd9956fb-c37f-46df-96ea-d0ff7a35e0f9
-- title:
--   Definitions bundle OAIQ091C020 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 195 declarations of OpenAI's Lean: 36 definitions, 1 inductive type or structure, 5 instances and 153 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.signedFirst`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalBundleExtension.signedTail`, `OAI.PositiveEinsteinFour.Geometry.OneFormExactEigenIndex`, `OAI.PositiveEinsteinFour.Geometry.ScalarBaseEigenIndex`, `OAI.PositiveEinsteinFour.Geometry.ScalarBaseSpectralSpace`, `OAI.PositiveEinsteinFour.Geometry.ScalarBaseSpectralValue`, `OAI.PositiveEinsteinFour.Geometry.ScalarEuclideanSobolev.constant`, `OAI.PositiveEinsteinFour.Geometry.ScalarEuclideanSobolev.coordinateL2`, `OAI.PositiveEinsteinFour.Geometry.ScalarEuclideanSobolev.gradientL2`, `OAI.PositiveEinsteinFour.Geometry.ScalarEuclideanSobolev.partialL2`, `OAI.PositiveEinsteinFour.Geometry.ScalarEuclideanSobolev.valueL2`, `OAI.PositiveEinsteinFour.Geometry.ScalarPartition`, `OAI.PositiveEinsteinFour.Geometry.ScalarPartition.center`, `OAI.PositiveEinsteinFour.Geometry.ScalarPartition.ι`, `OAI.PositiveEinsteinFour.Geometry.ScalarPartition.ρ`, `OAI.PositiveEinsteinFour.Geometry.TwoFormH1`, `OAI.PositiveEinsteinFour.Geometry.chartTwoFormConnection`, `OAI.PositiveEinsteinFour.Geometry.fourHeatCovariantDerivative`, `OAI.PositiveEinsteinFour.Geometry.fourHeatCovariantFlux`, `OAI.PositiveEinsteinFour.Geometry.fourHeatCovariantOperator`, `OAI.PositiveEinsteinFour.Geometry.fourHeatGaussianPolynomialTime`, `OAI.PositiveEinsteinFour.Geometry.fourHeatPolynomialTime`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseHeatRate`, `OAI.PositiveEinsteinFour.Geometry.scalarBasePullback`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseResolvent`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseShiftedSolution`, `OAI.PositiveEinsteinFour.Geometry.scalarCoercive_h1Inner`, `OAI.PositiveEinsteinFour.Geometry.scalarH1BaseValue`, `OAI.PositiveEinsteinFour.Geometry.scalarH1BaseValueFun`, `OAI.PositiveEinsteinFour.Geometry.smoothScalarBaseL2`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormCovariantEnergy`, `OAI.PositiveEinsteinFour.Geometry.twoFormCovariantPairing`, `OAI.PositiveEinsteinFour.Geometry.twoFormFramedRoughTrace`, `OAI.PositiveEinsteinFour.Geometry.twoFormFramedSecondDerivative`, `OAI.PositiveEinsteinFour.Geometry.twoFormLocalNabla`, `OAI.PositiveEinsteinFour.Geometry.twoFormLocalNablaRows`, `OAI.PositiveEinsteinFour.Geometry.twoFormSecondCovariantCoordinates`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C038` and `OAIQ091C018` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C039`, `OAIQ091C045`, `OAIQ091C046`, `OAIQ091C047`, `OAIQ091C049`, `OAIQ091C050`, `OAIQ091C051`, `OAIQ091C052`, `OAIQ091C053` and `OAIQ091C056`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C038
import Definitions.Def_OAIQ091C018

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Coordinate compatibility of the actual two-form covariant derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem TwoFormSmooth.covariant_contDiffAt {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (a : Fin 3 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => twoFormCovariantCoordinates o u c w a) z :=
  covariantDerivative_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne'
    _ (hu.coordinates_contDiffAt c z hz) a

theorem TwoFormSmooth.continuous_framedCovariantDerivative {o : FrameOrientation g}
    {u : M → TwoFormFour} (hu : TwoFormSmooth o u) :
    Continuous (twoFormFramedCovariantDerivative o u) := by
  apply continuous_framedTensor g (twoFormCovariantCoordinates o u)
  · intro c z hz a
    exact (hu.covariant_contDiffAt c z hz a).continuousAt
  · exact hu.covariant_transition

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual intrinsic covariant-derivative pairing of smooth two-forms.
The factor one-half removes the duplicated skew-tensor entries. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormCovariantPairing (o : FrameOrientation g) (u v : M → TwoFormFour) (x : M) : ℝ :=
  (1 / 2 : ℝ) * frameTensorPairing
    (twoFormFramedCovariantDerivative o u ⟨x, o.frame x⟩)
    (twoFormFramedCovariantDerivative o v ⟨x, o.frame x⟩)

theorem twoFormCovariantPairing_eq_frame (o : FrameOrientation g) (u v : M → TwoFormFour)
    (e : FrameBundle g) :
    twoFormCovariantPairing o u v e.base = (1 / 2 : ℝ) * frameTensorPairing
      (twoFormFramedCovariantDerivative o u e) (twoFormFramedCovariantDerivative o v e) := by
  unfold twoFormCovariantPairing twoFormFramedCovariantDerivative
  have he : e.frame.matrix = (o.frame e.base).matrix * (o.frame e.base).changeMatrix e.frame :=
    ((o.frame e.base).mul_changeMatrix e.frame).symm
  rw [he, frameTensor_mul, frameTensor_mul,
    frameTensor_pairing_orthogonal _
      (mul_eq_one_comm.mp ((o.frame e.base).changeMatrix_orthogonal e.frame))]

theorem twoFormCovariantPairing_comm (o : FrameOrientation g) (u v : M → TwoFormFour) (x : M) :
    twoFormCovariantPairing o u v x = twoFormCovariantPairing o v u x := by
  unfold twoFormCovariantPairing frameTensorPairing
  simp only [mul_comm]

theorem twoFormCovariantPairing_self_nonneg (o : FrameOrientation g) (u : M → TwoFormFour)
    (x : M) : 0 ≤ twoFormCovariantPairing o u u x := by
  unfold twoFormCovariantPairing frameTensorPairing
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun a _ => mul_self_nonneg _)

theorem TwoFormSmooth.covariantPairing_continuous {u v : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (hv : TwoFormSmooth o v) :
    Continuous (twoFormCovariantPairing o u v) := by
  let F : FrameBundle g → ℝ := fun e => (1 / 2 : ℝ) * frameTensorPairing
    (twoFormFramedCovariantDerivative o u e) (twoFormFramedCovariantDerivative o v e)
  have hF : Continuous F := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro a _
    exact ((continuous_apply a).comp hu.continuous_framedCovariantDerivative).mul
      ((continuous_apply a).comp hv.continuous_framedCovariantDerivative)
  apply continuous_iff_continuousAt.mpr
  intro c
  apply (hF.continuousAt.comp
    (continuousAt_localGramSection g c 1 (by simp))).congr_of_eventuallyEq
  filter_upwards [] with x
  change twoFormCovariantPairing o u v x = F (localGramSection g c 1 (by simp) x)
  have hx := twoFormCovariantPairing_eq_frame o u v (localGramSection g c 1 (by simp) x)
  rw [localGramSection_base] at hx
  exact hx

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.twoFormEnergy_probability
def smoothTwoFormCovariantEnergy (u v : smoothTwoForms o) : ℝ :=
  ∫ x, twoFormCovariantPairing o u.val v.val x ∂normalizedVolume g

theorem smoothTwoFormCovariantPairing_integrable (u v : smoothTwoForms o) :
    Integrable (twoFormCovariantPairing o u.val v.val) (normalizedVolume g) :=
  (u.property.covariantPairing_continuous v.property).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormCovariantEnergy_comm (u v : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy u v = smoothTwoFormCovariantEnergy v u := by
  apply integral_congr_ae
  filter_upwards [] with x
  exact twoFormCovariantPairing_comm o u.val v.val x

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormCovariantEnergy_nonneg (u : smoothTwoForms o) :
    0 ≤ smoothTwoFormCovariantEnergy u u :=
  integral_nonneg (twoFormCovariantPairing_self_nonneg o u.val)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Levi-Civita connection in a local Gram frame is skew.
Its action agrees with the Hodge-compatible fiber action. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem chartGramMatrix_det_ne_zero (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    (chartGramMatrix g c S z).det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse (chartGramMatrix_normalizes g c S hS ⟨z, hz⟩)

def chartTwoFormConnection (c : M) (S : Mat4) (i : Fin 4) (z : FourSpace) : Mat4 :=
  pulledConnection (chartGramMatrix g c S z) (matrixPartial (chartGramMatrix g c S) i z)
    (connectionMatrix g c i z)

theorem chartTwoFormConnection_equation (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (i : Fin 4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    chartGramMatrix g c S z * chartTwoFormConnection (g := g) c S i z =
      matrixPartial (chartGramMatrix g c S) i z +
        connectionMatrix g c i z * chartGramMatrix g c S z :=
  pulledConnection_equation _ _ _ (isUnit_iff_ne_zero.mpr (chartGramMatrix_det_ne_zero c S hS z hz))

theorem chartTwoFormConnection_skew (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (i : Fin 4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    (chartTwoFormConnection (g := g) c S i z)ᵀ = -chartTwoFormConnection (g := g) c S i z := by
  let G := chartGramMatrix g c S
  let H := metricInChart g c
  have hG (r s : Fin 4) : DifferentiableAt ℝ (fun w => G w r s) z :=
    (chartGramMatrix_contDiffAt g c S z hz r s).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hH (r s : Fin 4) : DifferentiableAt ℝ (fun w => H w r s) z :=
    (metricInChart_contDiffAt g c z hz r s).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hn : (G z)ᵀ * H z * G z = 1 := chartGramMatrix_normalizes g c S hS ⟨z, hz⟩
  have heq : (fun w => (G w)ᵀ * (H w * G w)) =ᶠ[𝓝 z] fun _ => 1 := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    simpa only [Matrix.mul_assoc] using chartGramMatrix_normalizes g c S hS ⟨w, hw⟩
  have hzero : matrixPartial (fun w => (G w)ᵀ * (H w * G w)) i z = 0 := by
    rw [matrixPartial_congr heq]
    ext r s
    change fderiv ℝ (fun _ : FourSpace => (1 : Mat4) r s) z (coordinateVector i) = 0
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
      (fderiv_const_apply (𝕜 := ℝ) (x := z) ((1 : Mat4) r s))
  have hd := matrixPartial_congruence G H z hG hH i
  rw [hzero] at hd
  have hm : matrixPartial H i z =
      (connectionMatrix g c i z)ᵀ * H z + H z * connectionMatrix g c i z :=
    matrixPartial_metric g c z (isUnit_iff_ne_zero.mpr (metricInChart_posDef g c z hz).det_pos.ne') i
  rw [hm] at hd
  have hc := pulledConnection_metric_compatibility (H z) (G z) (matrixPartial G i z)
    (connectionMatrix g c i z) (isUnit_iff_ne_zero.mpr (chartGramMatrix_det_ne_zero c S hS z hz))
  rw [hn, Matrix.mul_one, Matrix.one_mul] at hc
  apply eq_neg_of_add_eq_zero_left
  exact hc.trans hd.symm

theorem chartTwoFormConnection_as_twoForm (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (i : Fin 4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormMatrix (twoFormExtract (chartTwoFormConnection (g := g) c S i z)) =
      chartTwoFormConnection (g := g) c S i z :=
  twoFormMatrix_extract _ (chartTwoFormConnection_skew c S hS i z hz)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity of the actual smooth two-form covariant derivative and energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormCovariantPairing_add (u v w : smoothTwoForms o) (x : M) :
    twoFormCovariantPairing o (u + v).val w.val x =
      twoFormCovariantPairing o u.val w.val x + twoFormCovariantPairing o v.val w.val x := by
  unfold twoFormCovariantPairing
  rw [twoFormFramedCovariantDerivative_add]
  simp only [frameTensorPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

theorem twoFormCovariantPairing_smul (r : ℝ) (u v : M → TwoFormFour) (x : M) :
    twoFormCovariantPairing o (r • u) v x = r * twoFormCovariantPairing o u v x := by
  unfold twoFormCovariantPairing
  rw [twoFormFramedCovariantDerivative_smul]
  simp only [frameTensorPairing, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  ring

variable [T3Space M] [MeasurableSpace M] [BorelSpace M] [CompactSpace M] [Nonempty M]

theorem smoothTwoFormCovariantEnergy_add (u v w : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy (u + v) w =
      smoothTwoFormCovariantEnergy u w + smoothTwoFormCovariantEnergy v w := by
  unfold smoothTwoFormCovariantEnergy
  simp_rw [twoFormCovariantPairing_add]
  exact integral_add (smoothTwoFormCovariantPairing_integrable u w)
    (smoothTwoFormCovariantPairing_integrable v w)

omit [CompactSpace M] [Nonempty M] in
theorem smoothTwoFormCovariantEnergy_smul (r : ℝ) (u v : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy (r • u) v = r * smoothTwoFormCovariantEnergy u v := by
  change (∫ x, twoFormCovariantPairing o (r • u.val) v.val x ∂normalizedVolume g) = _
  simp_rw [twoFormCovariantPairing_smul]
  exact integral_const_mul _ _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The concrete two-form connection action in a local orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

theorem tensorSlotAction_twoForm (b a : TwoFormFour) :
    tensorSlotAction (twoFormMatrix b) (twoFormTensor a) = -twoFormTensor (twoFormSkewAction b a) := by
  funext v
  have hv : v = ![v 0, v 1] := by ext j; fin_cases j <;> rfl
  rw [hv]
  have hs : tensorSlotAction (twoFormMatrix b) (twoFormTensor a) ![v 0, v 1] =
      ((twoFormMatrix b)ᵀ * twoFormMatrix a + twoFormMatrix a * twoFormMatrix b) (v 0) (v 1) := by
    simp only [tensorSlotAction, covariantSlotAction, Fin.sum_univ_two,
      Function.update_self, twoFormTensor, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    simp [Fin.sum_univ_four, Function.update]
    ring
  rw [hs, twoFormMatrix_skew]
  change (-twoFormMatrix b * twoFormMatrix a + twoFormMatrix a * twoFormMatrix b) (v 0) (v 1) =
    -twoFormMatrix (twoFormSkewAction b a) (v 0) (v 1)
  rw [twoFormSkewAction_matrix]
  have hm : -twoFormMatrix b * twoFormMatrix a + twoFormMatrix a * twoFormMatrix b =
      -(twoFormMatrix b * twoFormMatrix a - twoFormMatrix a * twoFormMatrix b) := by noncomm_ring
  exact congrArg (fun A : Mat4 => A (v 0) (v 1)) hm

theorem tensorPartial_twoForm {a : FourSpace → TwoFormFour} {z : FourSpace}
    (ha : DifferentiableAt ℝ a z) (i : Fin 4) :
    tensorPartial (fun w => twoFormTensor (a w)) i z =
      twoFormTensor (fderiv ℝ a z (coordinateVector i)) := by
  funext v
  let L : TwoFormFour →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj v).comp twoFormTensorLinear.toContinuousLinearMap
  have h := (L.hasFDerivAt.comp z ha.hasFDerivAt).fderiv
  exact congrArg (fun D : FourSpace →L[ℝ] ℝ => D (coordinateVector i)) h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def twoFormLocalNabla (c : M) (S : Mat4) (a : FourSpace → TwoFormFour)
    (i : Fin 4) (z : FourSpace) : TwoFormFour :=
  fderiv ℝ a z (coordinateVector i) +
    twoFormSkewAction (twoFormExtract (chartTwoFormConnection (g := g) c S i z)) (a z)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual second covariant derivative and rough trace needed for
integration by parts on the two-form H1 completion. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormSecondCovariantCoordinates (o : FrameOrientation g) (u : M → TwoFormFour)
    (c : M) (z : FourSpace) : CovariantCoordinates 4 :=
  covariantDerivative g c (twoFormCovariantCoordinates o u c) z

theorem TwoFormSmooth.secondCovariant_contDiffAt {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (a : Fin 4 → Fin 4) :
    ContDiffAt ℝ ∞ (fun w => twoFormSecondCovariantCoordinates o u c w a) z :=
  covariantDerivative_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne'
    _ (hu.covariant_contDiffAt c z hz) a

theorem TwoFormSmooth.secondCovariant_transition {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c d : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target)
    (hx : (chartAt FourSpace c).symm z ∈ (chartAt FourSpace d).source) :
    twoFormSecondCovariantCoordinates o u c z = frameTensor (chartTransitionMatrix c d z)
      (twoFormSecondCovariantCoordinates o u d (chartTransition c d z)) := by
  apply covariantDerivative_chart_transition g c d _ _ z hz hx
  · intro a
    exact (hu.covariant_contDiffAt d _ ((chartAt FourSpace d).map_source hx) a).differentiableAt
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact (chart_overlap_eventually c d z hz hx).mono
      (fun w hw => hu.covariant_transition c d w hw.1 hw.2)

def twoFormFramedSecondDerivative (o : FrameOrientation g) (u : M → TwoFormFour)
    (e : FrameBundle g) : CovariantCoordinates 4 :=
  frameTensor e.frame.matrix
    (twoFormSecondCovariantCoordinates o u e.base (chartAt FourSpace e.base e.base))

theorem TwoFormSmooth.continuous_framedSecondDerivative {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) : Continuous (twoFormFramedSecondDerivative o u) := by
  apply continuous_framedTensor g (twoFormSecondCovariantCoordinates o u)
  · intro c z hz a
    exact (hu.secondCovariant_contDiffAt c z hz a).continuousAt
  · exact hu.secondCovariant_transition

theorem TwoFormSmooth.framedCovariant_parallel_derivative {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (γ : ℝ → FrameBundle g) (t : ℝ) (i : Fin 4)
    (hγ : ContinuousAt γ t) (hp : ParallelFrameCurveAt g γ i t) (a : Fin 3 → Fin 4) :
    HasDerivAt (fun s => twoFormFramedCovariantDerivative o u (γ s) a)
      (twoFormFramedSecondDerivative o u (γ t) (Fin.cons i a)) t := by
  apply hasDerivAt_framedTensor g (twoFormCovariantCoordinates o u)
  · intro c z hz a
    exact (hu.covariant_contDiffAt c z hz a).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact hu.covariant_transition
  · exact hu.secondCovariant_transition
  · exact hγ
  · exact hp

def twoFormFramedRoughTrace (o : FrameOrientation g) (u : M → TwoFormFour)
    (e : FrameBundle g) : CovariantCoordinates 2 :=
  fun a => ∑ i, twoFormFramedSecondDerivative o u e (Fin.cons i (Fin.cons i a))

theorem TwoFormSmooth.continuous_framedRoughTrace {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) : Continuous (twoFormFramedRoughTrace o u) := by
  apply continuous_pi
  intro a
  exact continuous_finsetSum _ (fun i _ => (continuous_apply _).comp hu.continuous_framedSecondDerivative)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Levi-Civita commutator on a smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.framed_commutator {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (e : FrameBundle g) (i j : Fin 4) (a : Fin 2 → Fin 4) :
    twoFormFramedSecondDerivative o u e (Fin.cons i (Fin.cons j a)) -
      twoFormFramedSecondDerivative o u e (Fin.cons j (Fin.cons i a)) =
        -tensorSlotAction (curvatureEndomorphism (frameCurvature g e.base e.frame) i j)
          (twoFormFramedValue o u e) a := by
  let c := e.base
  let z := chartAt FourSpace c c
  let T := twoFormCoordinates o u c z
  let X := twoFormSecondCovariantCoordinates o u c z
  let C := fun p q => coordinateCurvatureMatrix g c p q z
  have hz : z ∈ (chartAt FourSpace c).target := mem_chart_target FourSpace c
  have hX (p q : Fin 4) (b : Fin 2 → Fin 4) :
      X (Fin.cons p (Fin.cons q b)) - X (Fin.cons q (Fin.cons p b)) =
        -tensorSlotAction (C p q) T b :=
    covariantDerivative_commutator g c (twoFormCoordinates o u c) z hz
      (metricInChart_posDef g c z hz).det_pos.ne' (hu.coordinates_contDiffAt c z hz) p q b
  have h := framed_tensor_commutator e.frame.matrix
    (isUnit_iff_ne_zero.mpr e.frame.det_ne_zero) C T X hX i j a
  rw [frame_curvatureEndomorphism] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth lower-order coefficients of the actual two-form connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem chartTwoFormConnection_formula (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (i : Fin 4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    chartTwoFormConnection (g := g) c S i z =
      ((chartGramMatrix g c S z)ᵀ * metricInChart g c z) *
        (matrixPartial (chartGramMatrix g c S) i z +
          connectionMatrix g c i z * chartGramMatrix g c S z) := by
  have hn := chartGramMatrix_normalizes g c S hS ⟨z, hz⟩
  calc
    _ = 1 * chartTwoFormConnection (g := g) c S i z := (Matrix.one_mul _).symm
    _ = (((chartGramMatrix g c S z)ᵀ * metricInChart g c z) * chartGramMatrix g c S z) *
        chartTwoFormConnection (g := g) c S i z := by rw [hn]
    _ = _ := by rw [Matrix.mul_assoc, chartTwoFormConnection_equation c S hS i z hz]

theorem chartTwoFormConnection_contDiffAt (c : M) (S : Mat4) (hS : Sᵀ * S = 1)
    (i : Fin 4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (r s : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => chartTwoFormConnection (g := g) c S i w r s) z := by
  have hG (j k : Fin 4) := chartGramMatrix_contDiffAt g c S z hz j k
  have hM (j k : Fin 4) := metricInChart_contDiffAt g c z hz j k
  have hD (j k : Fin 4) : ContDiffAt ℝ ∞
      (fun w => matrixPartial (chartGramMatrix g c S) i w j k) z :=
    ((hG j k).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const
  have hC (j k : Fin 4) : ContDiffAt ℝ ∞ (fun w => connectionMatrix g c i w j k) z :=
    christoffel_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne' j i k
  have hL (j k : Fin 4) : ContDiffAt ℝ ∞
      (fun w => ((chartGramMatrix g c S w)ᵀ * metricInChart g c w) j k) z := by
    change ContDiffAt ℝ ∞ (fun w => ∑ l, chartGramMatrix g c S w l j * metricInChart g c w l k) z
    exact ContDiffAt.sum (fun l _ => (hG l j).mul (hM l k))
  have hR (j k : Fin 4) : ContDiffAt ℝ ∞
      (fun w => (matrixPartial (chartGramMatrix g c S) i w +
        connectionMatrix g c i w * chartGramMatrix g c S w) j k) z := by
    change ContDiffAt ℝ ∞ (fun w => matrixPartial (chartGramMatrix g c S) i w j k +
      ∑ l, connectionMatrix g c i w j l * chartGramMatrix g c S w l k) z
    exact (hD j k).add (ContDiffAt.sum (fun l _ => (hC j l).mul (hG l k)))
  have h : ContDiffAt ℝ ∞ (fun w => (((chartGramMatrix g c S w)ᵀ * metricInChart g c w) *
      (matrixPartial (chartGramMatrix g c S) i w +
        connectionMatrix g c i w * chartGramMatrix g c S w)) r s) z := by
    change ContDiffAt ℝ ∞ (fun w => ∑ l, ((chartGramMatrix g c S w)ᵀ * metricInChart g c w) r l *
      (matrixPartial (chartGramMatrix g c S) i w +
        connectionMatrix g c i w * chartGramMatrix g c S w) l s) z
    exact ContDiffAt.sum (fun l _ => (hL r l).mul (hR l s))
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact congrArg (fun A : Mat4 => A r s) (chartTwoFormConnection_formula c S hS i w hw)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric curvature defines an actual smooth endomorphism of global
two-form fields, independent of the chosen reference frames. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem chartMetricCurvature_contDiffAt (c : M) (S : Mat4) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (fun w => frameTensor (chartGramMatrix g c S w)
      (curvatureCoordinates g c w)) z := by
  apply contDiffAt_pi.mpr
  intro a
  unfold frameTensor
  apply ContDiffAt.sum
  intro b _
  exact (contDiffAt_prod fun k _ => chartGramMatrix_contDiffAt g c S z hz (b k) (a k)).mul
    (curvatureCoordinates_contDiffAt g c z hz (metricInChart_posDef g c z hz).det_pos.ne' b)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The completion in the actual two-form H1 norm and its bounded map to
L2. Injectivity of the map is not assumed; it requires the weak derivative
closure argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

instance smoothH1TwoFormInnerCore : InnerProductSpace.Core ℝ (SmoothH1TwoForm o) where
  inner u v := smoothTwoFormL2Inner (o := o) u v + smoothTwoFormCovariantEnergy (o := o) u v
  conj_inner_symm u v := by
    simpa only [conj_trivial] using congrArg₂ (· + ·)
      (smoothTwoFormL2Inner_comm (v : smoothTwoForms o) (u : smoothTwoForms o))
      (smoothTwoFormCovariantEnergy_comm (v : smoothTwoForms o) (u : smoothTwoForms o))
  re_inner_nonneg u := add_nonneg (smoothTwoFormL2Inner_nonneg u)
    (smoothTwoFormCovariantEnergy_nonneg u)
  add_left u v w := by
    exact (congrArg₂ (· + ·)
      (smoothTwoFormL2Inner_add (u : smoothTwoForms o) v w)
      (smoothTwoFormCovariantEnergy_add (u : smoothTwoForms o) v w)).trans
      (add_add_add_comm _ _ _ _)
  smul_left u v r := by
    change smoothTwoFormL2Inner (r • (u : smoothTwoForms o)) v +
      smoothTwoFormCovariantEnergy (r • (u : smoothTwoForms o)) v =
        r * (smoothTwoFormL2Inner u v + smoothTwoFormCovariantEnergy u v)
    exact (congrArg₂ (· + ·)
      (smoothTwoFormL2Inner_smul r (u : smoothTwoForms o) v)
      (smoothTwoFormCovariantEnergy_smul r (u : smoothTwoForms o) v)).trans
      (mul_add r _ _).symm
  definite u hu := by
    apply smoothTwoFormL2Inner_definite (u : smoothTwoForms o)
    have h₁ := smoothTwoFormL2Inner_nonneg (u : smoothTwoForms o)
    have h₂ := smoothTwoFormCovariantEnergy_nonneg (u : smoothTwoForms o)
    linarith

instance smoothH1TwoFormNormedAddCommGroup : NormedAddCommGroup (SmoothH1TwoForm o) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance smoothH1TwoFormInnerProductSpace : InnerProductSpace ℝ (SmoothH1TwoForm o) :=
  InnerProductSpace.ofCore _

def TwoFormH1 (o : FrameOrientation g) := UniformSpace.Completion (SmoothH1TwoForm o)
  deriving NormedAddCommGroup, NormedSpace ℝ, InnerProductSpace ℝ, CompleteSpace

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local Hodge-compatible connection formula is the actual
Levi-Civita derivative of each smooth two-form section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.localNabla_tensor {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target)
    (hp : ∀ w (hw : w ∈ U), chartGramSection g c S hS ⟨w, hUt hw⟩ ∈ o.positive)
    (z : FourSpace) (hzU : z ∈ U) (i : Fin 4) :
    frameTensor (chartGramMatrix g c S z)
      (tensorCovariantDirection (connectionMatrix g c) (twoFormCoordinates o u c) i z) =
        twoFormTensor (twoFormLocalNabla (g := g) c S (twoFormChartValue o u c S hS) i z) := by
  let G := chartGramMatrix g c S
  let T := twoFormCoordinates o u c
  let a := twoFormChartValue o u c S hS
  have hz := hUt hzU
  have hG (r s : Fin 4) : DifferentiableAt ℝ (fun w => G w r s) z :=
    (chartGramMatrix_contDiffAt g c S z hz r s).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hT (v : Fin 2 → Fin 4) : DifferentiableAt ℝ (fun w => T w v) z :=
    (hu.coordinates_contDiffAt c z hz v).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have ha : DifferentiableAt ℝ a z :=
    ((hu c S hS U hU hUt hp).contDiffAt (hU.mem_nhds hzU)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : (fun w => twoFormTensor (a w)) =ᶠ[𝓝 z] fun w => frameTensor (G w) (T w) := by
    filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
    exact twoFormChartValue_tensor o u c S hS w hw
  have hd : tensorPartial (fun w => twoFormTensor (a w)) i z =
      tensorPartial (fun w => frameTensor (G w) (T w)) i z := by
    funext v
    have hev : (fun w => twoFormTensor (a w) v) =ᶠ[𝓝 z]
        fun w => frameTensor (G w) (T w) v := he.mono (fun w hw => congrFun hw v)
    exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i))
      hev.fderiv_eq
  rw [tensorPartial_twoForm ha, tensorPartial_frameTensor G T z hG hT] at hd
  have hc := frameVariation_connection (G z) (matrixPartial G i z) (connectionMatrix g c i z)
    (chartTwoFormConnection (g := g) c S i z)
    (chartTwoFormConnection_equation c S hS i z hz) (T z)
  have haz : frameTensor (G z) (T z) = twoFormTensor (a z) := (he.self_of_nhds).symm
  rw [haz, ← chartTwoFormConnection_as_twoForm c S hS i z hz, tensorSlotAction_twoForm] at hc
  change frameTensor (G z) (tensorPartial T i z -
    tensorSlotAction (connectionMatrix g c i z) (T z)) =
      twoFormTensor (fderiv ℝ a z (coordinateVector i) +
        twoFormSkewAction (twoFormExtract (chartTwoFormConnection (g := g) c S i z)) (a z))
  have htadd (b d : TwoFormFour) : twoFormTensor (b + d) = twoFormTensor b + twoFormTensor d :=
    twoFormTensorLinear.map_add b d
  rw [htadd]
  funext v
  have hdv := congrFun hd v
  have hcv := congrFun hc v
  simp only [frameTensor_sub, Pi.add_apply, Pi.neg_apply] at hdv hcv ⊢
  linarith only [hdv, hcv]

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

def twoFormLocalNablaRows (c : M) (S : Mat4) (a : FourSpace → TwoFormFour)
    (z : FourSpace) (i : Fin 4) : TwoFormFour :=
  ∑ j, chartGramMatrix g c S z j i • twoFormLocalNabla (g := g) c S a j z

theorem TwoFormSmooth.gramCovariantDerivative {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (U : Set FourSpace) (hU : IsOpen U)
    (hUt : U ⊆ (chartAt FourSpace c).target)
    (hp : ∀ w (hw : w ∈ U), chartGramSection g c S hS ⟨w, hUt hw⟩ ∈ o.positive)
    (z : FourSpace) (hzU : z ∈ U) :
    twoFormFramedCovariantDerivative o u (chartGramSection g c S hS ⟨z, hUt hzU⟩) =
      twoFormDerivativeRows (twoFormLocalNablaRows (g := g) c S (twoFormChartValue o u c S hS) z) := by
  let x := (chartAt FourSpace c).symm z
  have hx : x ∈ (chartAt FourSpace x).source := mem_chart_source FourSpace x
  have ht := hu.covariant_transition c x z (hUt hzU) hx
  rw [chartTransitionMatrix_to_center c z (hUt hzU)] at ht
  change twoFormCovariantCoordinates o u c z = frameTensor (chartInverseMatrix c z)
    (twoFormCovariantCoordinates o u x (chartAt FourSpace x x)) at ht
  change frameTensor (chartInverseMatrix c z * chartGramMatrix g c S z)
    (twoFormCovariantCoordinates o u x (chartAt FourSpace x x)) = _
  rw [frameTensor_mul, ← ht]
  funext v
  obtain ⟨i, a, rfl⟩ := Fin.exists_cons v
  rw [frameTensor_cons, twoFormDerivativeRows_cons]
  change (∑ j, chartGramMatrix g c S z j i * frameTensor (chartGramMatrix g c S z)
    (fun w => covariantDerivative g c (twoFormCoordinates o u c) z (Fin.cons j w)) a) = _
  simp_rw [covariantDerivative_direction]
  simp_rw [hu.localNabla_tensor c S hS U hU hUt hp z hzU]
  change _ = twoFormTensorLinear (∑ j, chartGramMatrix g c S z j i •
    twoFormLocalNabla (g := g) c S (twoFormChartValue o u c S hS) j z) a
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The intrinsic first-derivative pairing in a chart. Its principal
coefficient is the actual inverse metric on each of the six components. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem chartGramMatrix_mul_transpose_orthogonal (g : SmoothMetric M) (c : M)
    (S : Mat4) (hS : Sᵀ * S = 1) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    chartGramMatrix g c S z * (chartGramMatrix g c S z)ᵀ = (metricInChart g c z)⁻¹ := by
  have he : chartGramMatrix g c S z = chartGramMatrix g c 1 z * S := by
    simp only [chartGramMatrix, Matrix.mul_one]
  rw [he, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc S,
    mul_eq_one_comm.mp hS, Matrix.one_mul]
  exact chartGramMatrix_mul_transpose g c z hz

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual scalar first jet and its Dirichlet pairing.  The Hilbert space
below is the closure of smooth first jets, with the value coordinate retained;
no solvability or elliptic estimate is built into its definition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable {μ : Measure (FrameBundle g)} [CompactSpace (FrameBundle g)] [IsFiniteMeasure μ]

instance scalarH1_complete (d : ParallelMetricData g μ) : CompleteSpace (scalarH1 d) :=
  (Submodule.isClosed_topologicalClosure
    (LinearMap.range (smoothScalarFirstJet d))).isComplete.completeSpace_coe

theorem scalarH1_inner (d : ParallelMetricData g μ) (u v : scalarH1 d) :
    inner ℝ u v = inner ℝ (scalarH1Value d u) (scalarH1Value d v) +
      ∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v) := by
  change (∑ j : Option (Fin 4), inner ℝ (u.val j) (v.val j)) = _
  rw [Fintype.sum_option]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Values in the first-jet completion are actual base scalars.  Pullback from
normalized Riemannian volume is an isometry with closed image, so this property
survives completion of the smooth scalar jets. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance scalarBase_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance scalarBase_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

def scalarBasePullback (g : SmoothMetric M) (o : FrameOrientation g) :
    Lp ℝ 2 (normalizedVolume g) →ₗᵢ[ℝ] ScalarL2 g (canonicalFrameMeasure g o) :=
  Lp.compMeasurePreservingₗᵢ ℝ FrameBundle.base (canonicalFrameMeasure_base g o)

theorem scalarBasePullback_closed (g : SmoothMetric M) (o : FrameOrientation g) :
    IsClosed (range (scalarBasePullback g o)) :=
  (scalarBasePullback g o).isometry.isClosedEmbedding.isClosed_range

def smoothScalarBaseL2 (g : SmoothMetric M) (a : SmoothScalar (M := M)) :
    Lp ℝ 2 (normalizedVolume g) :=
  ContinuousMap.toLp 2 (normalizedVolume g) ℝ ⟨a.val, a.property.continuous⟩

theorem scalarBasePullback_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (a : SmoothScalar (M := M)) :
    scalarBasePullback g o (smoothScalarBaseL2 g a) =
      smoothScalarValueL2 g (canonicalFrameMeasure g o) a := by
  apply Lp.ext
  have hcomp := (canonicalFrameMeasure_base g o).quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (⟨a.val, a.property.continuous⟩ : C(M, ℝ)))
  filter_upwards [Lp.coeFn_compMeasurePreserving (smoothScalarBaseL2 g a)
      (canonicalFrameMeasure_base g o), hcomp,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
      (smoothScalarValue g a)] with e h₁ h₂ h₃
  exact h₁.trans (h₂.trans h₃.symm)

/-- No extra dependence on the orthonormal frame appears in the value
coordinate when completing smooth scalar first jets. -/
theorem scalarH1_base_representative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d) :
    ∃ f : Lp ℝ 2 (normalizedVolume g), scalarBasePullback g o f = scalarH1Value d u := by
  let p₀ : ScalarJetL2 g (canonicalFrameMeasure g o) →L[ℝ]
      ScalarL2 g (canonicalFrameMeasure g o) :=
    PiLp.proj 2 (fun _ : Option (Fin 4) => ScalarL2 g (canonicalFrameMeasure g o)) none
  have hclosed : IsClosed {v : ScalarJetL2 g (canonicalFrameMeasure g o) |
      p₀ v ∈ range (scalarBasePullback g o)} :=
    (scalarBasePullback_closed g o).preimage p₀.continuous
  have hsub : closure (range (smoothScalarFirstJet d)) ⊆
      {v : ScalarJetL2 g (canonicalFrameMeasure g o) |
        p₀ v ∈ range (scalarBasePullback g o)} := by
    apply hclosed.closure_subset_iff.mpr
    rintro v ⟨a, rfl⟩
    exact ⟨smoothScalarBaseL2 g a, scalarBasePullback_smooth g o a⟩
  exact hsub u.property

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

local instance scalarCoercive_h1Space_r4eb3af_1 (d : ParallelMetricData g μ) :
    NormedSpace ℝ (scalarH1 d) := Submodule.normedSpace (𝕜 := ℝ) (scalarH1 d)
local instance scalarCoercive_meanZeroSpace_r4eb3af_1 (d : ParallelMetricData g μ) :
    NormedSpace ℝ (scalarH1MeanZero d) :=
  Submodule.normedSpace (𝕜 := ℝ) (scalarH1MeanZero d)
local instance scalarCoercive_h1Inner (d : ParallelMetricData g μ) :
    InnerProductSpace ℝ (scalarH1 d) := Submodule.innerProductSpace _

local instance scalarCoercive_meanZeroInner_r4eb3af_1 (d : ParallelMetricData g μ) :
    InnerProductSpace ℝ (scalarH1MeanZero d) := Submodule.innerProductSpace _
theorem scalarH1_norm_sq (d : ParallelMetricData g μ) (u : scalarH1 d) :
    ‖u‖ ^ 2 = ‖scalarH1Value d u‖ ^ 2 +
      ∑ i : Fin 4, ‖scalarH1Gradient d i u‖ ^ 2 := by
  calc
    ‖u‖ ^ 2 = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
    _ = _ := by rw [scalarH1_inner]; simp only [real_inner_self_eq_norm_sq]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite tensor estimates for the chart localization of two-forms.
The bounds involve the actual value and covariant energy density. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory Set
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.gramCovariantCoordinates {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    twoFormFramedCovariantDerivative o u (chartGramSection g c 1 (by simp) ⟨z, hz⟩) =
      frameTensor (chartGramMatrix g c 1 z) (twoFormCovariantCoordinates o u c z) := by
  let x := (chartAt FourSpace c).symm z
  have ht := hu.covariant_transition c x z hz (mem_chart_source FourSpace x)
  rw [chartTransitionMatrix_to_center c z hz] at ht
  change twoFormCovariantCoordinates o u c z = frameTensor (chartInverseMatrix c z)
    (twoFormCovariantCoordinates o u x (chartAt FourSpace x x)) at ht
  change frameTensor (chartInverseMatrix c z * chartGramMatrix g c 1 z)
    (twoFormCovariantCoordinates o u x (chartAt FourSpace x x)) = _
  rw [frameTensor_mul, ← ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The base L² representative of an intrinsic H¹ scalar is a bounded
linear map, obtained from the closed image of base pullback. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]

local instance h1Base_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

def scalarH1BaseValueFun (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d) :
    Lp ℝ 2 (normalizedVolume g) :=
  Classical.choose (scalarH1_base_representative g o d u)

theorem scalarH1BaseValueFun_spec (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (u : scalarH1 d) :
    scalarBasePullback g o (scalarH1BaseValueFun g o d u) = scalarH1Value d u :=
  Classical.choose_spec (scalarH1_base_representative g o d u)

def scalarH1BaseValue (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    scalarH1 d →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  LinearMap.mkContinuous
    { toFun := scalarH1BaseValueFun g o d
      map_add' := fun u v => by
        apply (scalarBasePullback g o).injective
        rw [map_add, scalarH1BaseValueFun_spec, scalarH1BaseValueFun_spec,
          scalarH1BaseValueFun_spec, map_add]
      map_smul' := fun r u => by
        apply (scalarBasePullback g o).injective
        rw [map_smul, scalarH1BaseValueFun_spec, scalarH1BaseValueFun_spec, map_smul]
        rfl }
    1 (fun u => by
      change ‖scalarH1BaseValueFun g o d u‖ ≤ 1 * ‖u‖
      rw [one_mul, ← (scalarBasePullback g o).norm_map, scalarH1BaseValueFun_spec]
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      rw [scalarH1_norm_sq]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => sq_nonneg _)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The traced second covariant derivative is an actual smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.secondGram_contDiffAt {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (c : M) (S : Mat4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (fun w => frameTensor (chartGramMatrix g c S w)
      (twoFormSecondCovariantCoordinates o u c w)) z := by
  apply contDiffAt_pi.mpr
  intro a
  unfold frameTensor
  exact ContDiffAt.sum (fun b _ =>
    (contDiffAt_prod (fun k _ => chartGramMatrix_contDiffAt g c S z hz (b k) (a k))).mul
      (hu.secondCovariant_contDiffAt c z hz b))

theorem TwoFormSmooth.framedSecond_chart {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (z : ChartTarget c) :
    twoFormFramedSecondDerivative o u (chartGramSection g c S hS z) =
      frameTensor (chartGramMatrix g c S z) (twoFormSecondCovariantCoordinates o u c z) := by
  have hc := hu.secondCovariant_transition c ((chartAt FourSpace c).symm z) z z.property
    (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rw [chartTransitionMatrix_to_center c z z.property] at hc
  rw [hc, ← frameTensor_mul]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Gauss' lemma in every initial direction and the resulting radial speed bound. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix
open scoped Manifold ContDiff _root_.Topology InnerProductSpace

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem directionRotation_first (q : Directions) :
    orthogonalEuclideanIsometry (orientedToOrthogonal (directionOrientedMatrix q)).val
      (orientedToOrthogonal (directionOrientedMatrix q)).property (coordinateVector 0) = q.val := by
  ext i
  change (directionFrameMatrix q *ᵥ Pi.single 0 1) i = q.val i
  rw [Matrix.mulVec_single_one]
  exact directionFrameMatrix_zero q i

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The derivative-slot correction in the covariant Hessian trace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heat_framed_twoFormSecondTrace (g : SmoothMetric M) (c : M)
    (T : FourSpace → CovariantCoordinates 2) (E H : Mat4) (x : FourSpace)
    (hH : Hᵀ = H) (a : Fin 2 → Fin 4) :
    frameTensor E (twoFormSecondTrace H (covariantDerivative g c
      (covariantDerivative g c T) x)) a =
      ∑ p, ∑ q, H p q * (frameTensor E
        (tensorCovariantDirection (connectionMatrix g c)
          (tensorCovariantDirection (connectionMatrix g c) T p) q x) a -
        ∑ r, christoffel g c x r p q *
          frameTensor E (tensorCovariantDirection (connectionMatrix g c) T r x) a) := by
  have hsym (p q : Fin 4) : H q p = H p q := congrArg (fun A : Mat4 => A p q) hH
  unfold twoFormSecondTrace
  rw [frameTensor_sum]
  simp_rw [frameTensor_sum, frameTensor_const_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [hsym, heat_framed_second_covariant]
  have hc (r : Fin 4) : christoffel g c x r q p = christoffel g c x r p q :=
    christoffel_comm g c x r q p
  simp only [hc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame rough operator is the actual metric trace of the
covariant Hessian once the proved metric and drift transport laws apply. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormal_rough_pullback (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (T : FourSpace → CovariantCoordinates 2)
    (x : FourSpace) (hP : ContDiffAt ℝ 2 P x)
    (hT : ∀ z ∈ (chartAt FourSpace c).target, ∀ a, ContDiffAt ℝ ∞ (fun y => T y a) z)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (A : Mat4) (b : Fin 4 → ℝ)
    (hA : jacobianMatrix (fun y => (P y).1) x * A *
      (jacobianMatrix (fun y => (P y).1) x)ᵀ = (metricInChart g c (P x).1)⁻¹)
    (hb : ∀ r, (∑ i, jacobianMatrix (fun y => (P y).1) x r i * b i) -
      (∑ i, ∑ j, A i j * partialDeriv
        (fun y => jacobianMatrix (fun z => (P z).1) y r j) i x) =
      ∑ p, ∑ q, (metricInChart g c (P x).1)⁻¹ p q * christoffel g c (P x).1 r p q)
    (v : Fin 2 → Fin 4) :
    -(∑ i, ∑ j, A i j * tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i) j x v) +
      (∑ i, b i * tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i x v) =
    -frameTensor (P x).2 (twoFormSecondTrace (metricInChart g c (P x).1)⁻¹
      (covariantDerivative g c (covariantDerivative g c T) (P x).1)) v := by
  let J := jacobianMatrix (fun y => (P y).1)
  let H := (metricInChart g c (P x).1)⁻¹
  let S := fun r => frameTensor (P x).2
    (tensorCovariantDirection (connectionMatrix g c) T r (P x).1) v
  let Q : Mat4 := Matrix.of fun r s => frameTensor (P x).2
    (tensorCovariantDirection (connectionMatrix g c)
      (tensorCovariantDirection (connectionMatrix g c) T r) s (P x).1) v
  have hPd := hP.differentiableAt (by norm_num)
  have hf (i : Fin 4) : tensorCovariantDirection (heatNormalFrameConnection g c P)
      (fun y => frameTensor (P y).2 (T (P y).1)) i x v = ∑ r, J x r i * S r := by
    have h := heatNormal_covariant_pullback g c P T x hPd
      (fun a => (hT _ hx a).differentiableAt (by simp)) hG.self_of_nhds i
    rw [h]
    simp_rw [← heatFrame_baseJacobian P x hPd]
    exact heat_frameTensor_weighted_sum _ _ _ v
  have hs (i j : Fin 4) : tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (T (P y).1)) i) j x v =
      (∑ r, partialDeriv (fun y => J y r i) j x * S r) +
        ∑ r, ∑ s, J x r i * J x s j * Q r s := by
    rw [heatNormal_covariant_second_pullback g c P T x hP hT hx hG i j]
    simp only [heat_frameTensor_weighted_sum, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    change J x r i * (J x s j * Q r s) = _
    ring
  simp_rw [hf, hs]
  have h := heat_rough_trace_algebra (J x) A H Q
    (fun i => matrixPartial J i x) b S
    (fun r => ∑ p, ∑ q, H p q * christoffel g c (P x).1 r p q) hA
    (fun i j r => heatJacobian_partials_commute hP.fst r j i) hb
  simp only [matrixPartial] at h
  rw [h, heat_connection_trace_expand]
  have hH : Hᵀ = H := by
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    ext i j
    exact metricInChart_comm g c (P x).1 j i
  rw [heat_framed_twoFormSecondTrace g c T (P x).2 H (P x).1 hH v]
  rfl

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


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

local instance chartEnergy_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

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

local instance chartH1_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual base L² scalars restrict continuously to compact metric charts.
This map identifies the chart value of every intrinsic H¹ scalar. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance chartValue_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

local instance chartValue_baseProbability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The critical Euclidean H1-to-L4 estimate needed by the compact
four-dimensional scalar minimization. The constant here is not sharp;
sharpness on the manifold comes from the nonlinear rigidity argument. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped ENNReal NNReal

noncomputable section

namespace ScalarEuclideanSobolev

local notation "V" => FourSpace

def constant : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure V) 2

theorem gradient_eLpNorm {f : V → ℝ} (hf : ContDiff ℝ 1 f) :
    eLpNorm (Euclidean.grad f) 2 volume = eLpNorm (fderiv ℝ f) 2 volume := by
  apply eLpNorm_congr_norm_ae
  filter_upwards with x
  exact (InnerProductSpace.toDual ℝ V).symm.norm_map (fderiv ℝ f x)

/-- The gradient in the existing Lebesgue measurable space of `FourSpace`. -/
def gradientL2 (f : ↥(Euclidean.C1c (E := V))) : Lp V 2 (volume : Measure V) :=
  ((Euclidean.continuous_grad f.property.1).memLp_of_hasCompactSupport
    (Euclidean.hasCompactSupport_grad f.property.2)).toLp _

end ScalarEuclideanSobolev

end
end PositiveEinsteinFour.Geometry
end


section

/-! Coordinate form of the Euclidean Sobolev estimate. The finite sum of
the four partial L² norms controls the gradient L² norm. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped ENNReal

noncomputable section

namespace ScalarEuclideanSobolev

theorem fderiv_norm_le_sum_partial (f : FourSpace → ℝ) (z : FourSpace) :
    ‖fderiv ℝ f z‖ ≤ ∑ i : Fin 4, ‖partialDeriv f i z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun i _ => norm_nonneg _))).mp
  have he := (EuclideanSpace.basisFun (Fin 4) ℝ).norm_dual (fderiv ℝ f z)
  have hb (i : Fin 4) : (EuclideanSpace.basisFun (Fin 4) ℝ) i = coordinateVector i := by
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  simp only [hb] at he
  change ‖fderiv ℝ f z‖ ^ 2 = ∑ i : Fin 4, (partialDeriv f i z) ^ 2 at he
  rw [he]
  simpa only [Real.norm_eq_abs, sq_abs] using
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun i : Fin 4 => ‖partialDeriv f i z‖) (fun i _ => norm_nonneg _))

theorem continuous_partial {f : FourSpace → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 4) :
    Continuous (partialDeriv f i) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

def partialL2 (f : ↥(Euclidean.C1c (E := FourSpace))) (i : Fin 4) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  ((continuous_partial f.property.1 i).memLp_of_hasCompactSupport
    (f.property.2.fderiv_apply ℝ (coordinateVector i))).toLp _

theorem partialL2_coe (f : ↥(Euclidean.C1c (E := FourSpace))) (i : Fin 4) :
    partialL2 f i =ᵐ[volume] partialDeriv f.val i := MemLp.coeFn_toLp _

theorem gradientL2_norm_le_sum (f : ↥(Euclidean.C1c (E := FourSpace))) :
    ‖gradientL2 f‖ ≤ ∑ i : Fin 4, ‖partialL2 f i‖ := by
  have hb : eLpNorm (fderiv ℝ f.val) 2 volume ≤
      ∑ i : Fin 4, eLpNorm (partialDeriv f.val i) 2 volume := by
    calc
      _ ≤ eLpNorm (fun z => ∑ i : Fin 4, ‖partialDeriv f.val i z‖) 2 volume :=
        eLpNorm_mono_real
          (fderiv_norm_le_sum_partial f.val)
      _ ≤ ∑ i : Fin 4, eLpNorm (fun z => ‖partialDeriv f.val i z‖) 2 volume := by
        have he : (fun z => ∑ i : Fin 4, ‖partialDeriv f.val i z‖) =
            (∑ i : Fin 4, fun z => ‖partialDeriv f.val i z‖) := by
          funext z
          simp only [Finset.sum_apply]
        rw [he]
        exact (eLpNorm_sum_le (hfs := fun i _ => by first | exact (((f.property.1.continuous_fderiv one_ne_zero).clm_apply continuous_const : Continuous fun z => fderiv ℝ f.val z (coordinateVector i)).norm).aestronglyMeasurable | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) (μ := (volume : Measure FourSpace)) (p := 2)
            (f := fun i : Fin 4 => fun z => ‖partialDeriv f.val i z‖)
            (s := Finset.univ) (by norm_num))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact eLpNorm_norm _
  have ht : (∑ i : Fin 4, eLpNorm (partialDeriv f.val i) 2 volume) ≠ (∞ : ℝ≥0∞) := by
    apply ne_of_lt
    exact ENNReal.sum_lt_top.mpr (fun i _ =>
      ((continuous_partial f.property.1 i).memLp_of_hasCompactSupport
        (f.property.2.fderiv_apply ℝ (coordinateVector i))).eLpNorm_lt_top)
  have hr := ENNReal.toReal_mono ht hb
  rw [← gradient_eLpNorm f.property.1] at hr
  simpa only [gradientL2, partialL2, Lp.norm_toLp, ENNReal.toReal_sum
    (fun i _ => ((continuous_partial f.property.1 i).memLp_of_hasCompactSupport
      (f.property.2.fderiv_apply ℝ (coordinateVector i))).eLpNorm_ne_top)] using hr

end ScalarEuclideanSobolev

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

/-! Actual smooth chart cutoffs obtained from a finite smooth partition
of unity. Their compact supports lie in the coordinate chart targets. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

/-- A finite set of chart centers with subordinate smooth weights. -/
structure ScalarPartition (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] where
  centers : Finset M
  weights : SmoothPartitionOfUnity {x : M // x ∈ centers} I4 M univ
  subordinate : weights.IsSubordinate (fun x => (chartAt FourSpace x.val).source)

namespace ScalarPartition

abbrev ι (P : ScalarPartition M) := {x : M // x ∈ P.centers}

instance instFintypeι (P : ScalarPartition M) : Fintype P.ι := Finset.Subtype.fintype P.centers

abbrev center (P : ScalarPartition M) (i : P.ι) : M := i.val

abbrev ρ (P : ScalarPartition M) := P.weights

end ScalarPartition

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Euclidean value and gradient of a compact chart cutoff form
a continuous first-jet map on intrinsic scalar H¹. All L² spaces use the
existing measurable structure and Lebesgue measure of `FourSpace`. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff ENNReal BigOperators

noncomputable section

namespace ScalarEuclideanSobolev

def valueL2 (f : ↥(Euclidean.C1c (E := FourSpace))) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  (f.property.1.continuous.memLp_of_hasCompactSupport f.property.2).toLp f.val

theorem valueL2_coe (f : ↥(Euclidean.C1c (E := FourSpace))) :
    valueL2 f =ᵐ[volume] f.val := MemLp.coeFn_toLp _

/-- Insert one scalar L² function in a Euclidean coordinate direction. -/
def coordinateL2 (i : Fin 4) :
    Lp ℝ 2 (volume : Measure FourSpace) →L[ℝ] Lp FourSpace 2 (volume : Measure FourSpace) :=
  (ContinuousLinearMap.toSpanSingleton ℝ ((EuclideanSpace.basisFun (Fin 4) ℝ) i)).compLpL 2 volume

theorem coordinateL2_coe (i : Fin 4) (f : Lp ℝ 2 (volume : Measure FourSpace)) :
    coordinateL2 i f =ᵐ[volume]
      fun z => f z • (EuclideanSpace.basisFun (Fin 4) ℝ) i :=
  (ContinuousLinearMap.toSpanSingleton ℝ ((EuclideanSpace.basisFun (Fin 4) ℝ) i)).coeFn_compLpL f

theorem grad_eq_sum_partial (f : FourSpace → ℝ) (z : FourSpace) :
    Euclidean.grad f z =
      ∑ i : Fin 4, partialDeriv f i z • (EuclideanSpace.basisFun (Fin 4) ℝ) i := by
  have hb (i : Fin 4) :
      (EuclideanSpace.basisFun (Fin 4) ℝ) i = coordinateVector i := by
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  calc
    _ = ∑ i : Fin 4, inner ℝ ((EuclideanSpace.basisFun (Fin 4) ℝ) i)
        (Euclidean.grad f z) • (EuclideanSpace.basisFun (Fin 4) ℝ) i :=
      ((EuclideanSpace.basisFun (Fin 4) ℝ).sum_repr' _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [real_inner_comm, hb]
      exact InnerProductSpace.toDual_symm_apply

theorem gradientL2_eq_sum_partialL2 (f : ↥(Euclidean.C1c (E := FourSpace))) :
    gradientL2 f = ∑ i : Fin 4, coordinateL2 i (partialL2 f i) := by
  apply Lp.ext
  have hall : ∀ᵐ z ∂(volume : Measure FourSpace), ∀ i : Fin 4,
      coordinateL2 i (partialL2 f i) z =
        partialDeriv f.val i z • (EuclideanSpace.basisFun (Fin 4) ℝ) i := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [coordinateL2_coe i (partialL2 f i), partialL2_coe f i] with z hc hp
    exact hc.trans (congrArg (fun r => r • (EuclideanSpace.basisFun (Fin 4) ℝ) i) hp)
  have hg : gradientL2 f =ᵐ[volume] Euclidean.grad f.val := MemLp.coeFn_toLp _
  filter_upwards [hg, hall,
    Lp.coeFn_finsetSum Finset.univ (fun i : Fin 4 => coordinateL2 i (partialL2 f i))]
      with z hgz hz hsum
  rw [hgz, hsum]
  change Euclidean.grad f.val z = ∑ i : Fin 4, coordinateL2 i (partialL2 f i) z
  simp_rw [hz]
  exact grad_eq_sum_partial f.val z

end ScalarEuclideanSobolev

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance euclideanJet_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual derivatives of a Gaussian with a smooth scalar amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff BigOperators

noncomputable section

theorem fourHeatGaussian_amplitude_time (t : ℝ) (ht : 0 < t)
    (u : FourSpace → ℝ) (x : FourSpace) :
    HasDerivAt (fun s => fourHeatGaussian s x * u x)
      (fourHeatGaussian t x * (‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t) * u x) t := by
  convert (fourHeatGaussian_hasDerivAt_time t ht x).mul_const (u x) using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth scalar multiplication and the finite partition identity for
actual smooth two-form sections. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormFrameValue_mul (ρ : M → ℝ) (u : M → TwoFormFour) (e : FrameBundle g) :
    twoFormFrameValue o (fun x => ρ x • u x) e = ρ e.base • twoFormFrameValue o u e :=
  (twoFormFrameActionLinear _).map_smul _ _

theorem twoFormChartValue_mul (ρ : M → ℝ) (u : M → TwoFormFour) (c : M)
    (S : Mat4) (hS : Sᵀ * S = 1) :
    twoFormChartValue o (fun x => ρ x • u x) c S hS =
      fun z => ρ ((chartAt FourSpace c).symm z) • twoFormChartValue o u c S hS z := by
  funext z
  by_cases hz : z ∈ (chartAt FourSpace c).target
  · simp only [twoFormChartValue, dite_eq_left hz, twoFormFrameValue_mul]
    rfl
  · simp only [twoFormChartValue, dite_eq_right hz, smul_zero]

theorem TwoFormSmooth.mul {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    {ρ : M → ℝ} (hρ : ContMDiff I4 𝓘(ℝ, ℝ) ∞ ρ) :
    TwoFormSmooth o (fun x => ρ x • u x) := by
  intro c S hS U hU hUt hp
  rw [twoFormChartValue_mul]
  apply ContDiffOn.fun_smul _ (hu c S hS U hU hUt hp)
  intro z hz
  exact (scalarCoordinates_contDiffAt hρ c z (hUt hz) (fun j => Fin.elim0 j)).contDiffWithinAt

end
end PositiveEinsteinFour.Geometry
end


section

/-! Consequences of the radial metric identity for the actual coordinate
derivatives in a divergence-form heat operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped _root_.Topology BigOperators

noncomputable section

theorem fourHeat_radial_derivative (f : FourSpace → ℝ) (x : FourSpace) :
    fderiv ℝ f x x = ∑ i : Fin 4, x i * partialDeriv f i x := by
  have hx : x = ∑ i : Fin 4, x i • coordinateVector i := by
    simpa only [WithLp.toLp_ofLp] using (sum_coordinateVector (WithLp.ofLp x)).symm
  let D : FourSpace →L[ℝ] ℝ := fderiv ℝ f x
  change D x = _
  rw [congrArg D hx]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, partialDeriv]
  rfl

theorem fourHeat_radial_divergence (a : FourSpace → Mat4) (x : FourSpace)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hrad : ∀ᶠ y in 𝓝 x, ∀ i, ∑ j : Fin 4, a y i j * y j = y i) :
    (∑ i : Fin 4, ∑ j : Fin 4, partialDeriv (fun y => a y i j) i x * x j) +
      (∑ i : Fin 4, a x i i) = 4 := by
  have hrow (i : Fin 4) :
      (∑ j : Fin 4, partialDeriv (fun y => a y i j) i x * x j) + a x i i = 1 := by
    let π : Fin 4 → FourSpace →L[ℝ] ℝ := fun j => PiLp.proj 2 (fun _ : Fin 4 => ℝ) j
    have hd := HasFDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => (ha i j).hasFDerivAt.mul ((π j).hasFDerivAt (x := x)))
    have heq : (fun y : FourSpace => y i) =ᶠ[𝓝 x]
        (fun y => ∑ j : Fin 4, a y i j * y j) := by
      filter_upwards [hrad] with y hy
      exact (hy i).symm
    have hD := (hd.congr_of_eventuallyEq heq).unique ((π i).hasFDerivAt (x := x))
    have h := congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) hD
    simp only [_root_.sum_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul,
      π, PiLp.proj_apply] at h
    have hcoord (j : Fin 4) : (coordinateVector i) j = if j = i then 1 else 0 := by
      simp [coordinateVector, eq_comm]
    simp only [hcoord, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true] at h
    simpa only [mul_comm, add_comm, partialDeriv] using h
  calc
    _ = ∑ i : Fin 4,
        ((∑ j : Fin 4, partialDeriv (fun y => a y i j) i x * x j) + a x i i) :=
      (Finset.sum_add_distrib).symm
    _ = ∑ _i : Fin 4, (1 : ℝ) := Finset.sum_congr rfl (fun i _ => hrow i)
    _ = 4 := by norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local six-component heat operator in a radial frame. The additional
first-order Gaussian term vanishes by the radial connection identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatBundleZero_gaussian (C : HeatMat6) (t : ℝ)
    (u : FourSpace → Fin 6 → ℝ) (x : FourSpace) (k : Fin 6) :
    fourHeatBundleZero C (fun y l => fourHeatGaussian t y * u y l) x k =
      fourHeatGaussian t x * fourHeatBundleZero C u x k := by
  unfold fourHeatBundleZero
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The leading scalar heat transport equation in density divergence form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped _root_.Topology BigOperators

noncomputable section

theorem fourHeatDensityDrift_radial (a : FourSpace → Mat4) (J : FourSpace → ℝ)
    (x : FourSpace) (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hrad : ∀ᶠ y in 𝓝 x, ∀ i, ∑ j : Fin 4, a y i j * y j = y i) :
    (∑ j : Fin 4, fourHeatDensityDrift a J x j * x j) =
      (∑ i : Fin 4, a x i i) - 4 - fderiv ℝ J x x / J x := by
  have hdiv := fourHeat_radial_divergence a x ha hrad
  have hcontract : (∑ j : Fin 4, (∑ i : Fin 4, a x i j * partialDeriv J i x) * x j) =
      fderiv ℝ J x x := by
    rw [fourHeat_radial_derivative]
    calc
      _ = ∑ i : Fin 4, (∑ j : Fin 4, a x i j * x j) * partialDeriv J i x := by
        norm_num [Fin.sum_univ_four]
        ring
      _ = _ := by simp_rw [hrad.self_of_nhds]
  have hb : (∑ j : Fin 4, fourHeatDensityDrift a J x j * x j) =
      -(∑ i : Fin 4, ∑ j : Fin 4, partialDeriv (fun y => a y i j) i x * x j) -
        (J x)⁻¹ * (∑ j : Fin 4, (∑ i : Fin 4, a x i j * partialDeriv J i x) * x j) := by
    norm_num [fourHeatDensityDrift, Fin.sum_univ_four]
    ring
  rw [hb, hcontract, div_eq_mul_inv]
  nlinarith only [hdiv]

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

local instance baseResolvent_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarBaseShiftedSolution : Lp ℝ 2 (normalizedVolume g) →L[ℝ] scalarH1 d :=
  (scalarH1BaseValue g o d).adjoint

def scalarBaseResolvent : Lp ℝ 2 (normalizedVolume g) →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (scalarH1BaseValue g o d).comp (scalarBaseShiftedSolution g o d)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Ordinary derivatives of local frame coefficients and their exact
relation to the actual covariant derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.gramTensor_contDiffAt {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (c : M) (S : Mat4) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (fun w => frameTensor (chartGramMatrix g c S w)
      (twoFormCoordinates o u c w)) z := by
  apply contDiffAt_pi.mpr
  intro a
  unfold frameTensor
  exact ContDiffAt.sum (fun b _ =>
    (contDiffAt_prod (fun k _ => chartGramMatrix_contDiffAt g c S z hz (b k) (a k))).mul
      (hu.coordinates_contDiffAt c z hz b))

theorem TwoFormSmooth.chartValue_contDiffAt {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ ∞ (twoFormChartValue o u c S hS) z := by
  let L : CovariantCoordinates 2 →L[ℝ] TwoFormFour :=
    (twoFormExtractLinear.comp twoTensorMatrixLinear).toContinuousLinearMap
  have h := L.contDiff.comp_contDiffAt z (hu.gramTensor_contDiffAt c S z hz)
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt FourSpace c).open_target.mem_nhds hz] with w hw
  exact twoFormChartValue_extract u c S hS w hw

theorem TwoFormSmooth.gramCovariantDirection {u : M → TwoFormFour} (hu : TwoFormSmooth o u)
    (c : M) (S : Mat4) (hS : Sᵀ * S = 1) (z : FourSpace)
    (hz : z ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    frameTensor (chartGramMatrix g c S z)
      (tensorCovariantDirection (connectionMatrix g c) (twoFormCoordinates o u c) i z) =
      tensorPartial (fun w => frameTensor (chartGramMatrix g c S w)
        (twoFormCoordinates o u c w)) i z -
      tensorSlotAction (chartTwoFormConnection (g := g) c S i z)
        (frameTensor (chartGramMatrix g c S z) (twoFormCoordinates o u c z)) := by
  let G := chartGramMatrix g c S
  let T := twoFormCoordinates o u c
  have hG (r s : Fin 4) : DifferentiableAt ℝ (fun w => G w r s) z :=
    (chartGramMatrix_contDiffAt g c S z hz r s).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hT (a : Fin 2 → Fin 4) : DifferentiableAt ℝ (fun w => T w a) z :=
    (hu.coordinates_contDiffAt c z hz a).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd := tensorPartial_frameTensor G T z hG hT i
  have hc := frameVariation_connection (G z) (matrixPartial G i z) (connectionMatrix g c i z)
    (chartTwoFormConnection (g := g) c S i z)
    (chartTwoFormConnection_equation c S hS i z hz) (T z)
  funext a
  have hda := congrFun hd a
  have hca := congrFun hc a
  change frameTensor (G z) (tensorPartial T i z - tensorSlotAction (connectionMatrix g c i z) (T z)) a =
    tensorPartial (fun w => frameTensor (G w) (T w)) i z a -
      tensorSlotAction (chartTwoFormConnection (g := g) c S i z) (frameTensor (G z) (T z)) a
  simp only [frameTensor_sub, Pi.add_apply] at hda hca ⊢
  linarith only [hda, hca]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Lower-order coefficients contributed by the normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOneConnectionFirst_radial (a : Mat4) (A : Fin 4 → Mat4)
    (x : FourSpace) (ha : ∀ j, (∑ i : Fin 4, a i j * x i) = x j)
    (hA : (∑ i : Fin 4, x i • A i) = 0) :
    (∑ i : Fin 4, x i • fourHeatOneConnectionFirst a A i) = 0 := by
  ext k l
  have hAl : (∑ j : Fin 4, x j * A j k l) = 0 := by
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
      using congrArg (fun T : Mat4 => T k l) hA
  change (∑ i : Fin 4, x i * ((-2 : ℝ) * ∑ j : Fin 4, a i j * A j k l)) = 0
  calc
    _ = (-2 : ℝ) * ∑ j : Fin 4, (∑ i : Fin 4, a i j * x i) * A j k l := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by simp_rw [ha]; rw [hAl]; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The regular radial average solves the successive transport equation,
with its coefficient at the origin fixed by the source. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped ContDiff Interval

noncomputable section

theorem fourHeatRadialAverage_zero (m : ℕ) (f : FourSpace → ℝ) :
    fourHeatRadialAverage m f 0 = f 0 / (m + 1 : ℝ) := by
  unfold fourHeatRadialAverage
  simp only [smul_zero]
  rw [intervalIntegral.integral_mul_const, integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero m), sub_zero]
  ring

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

local instance baseSpectrum_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar part of the Hodge complex has a genuine complete Hilbert
basis of shifted-Laplacian eigenvectors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance baseEigenbasis_frameCompact_r4eb3af_1 (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g
abbrev ScalarBaseSpectralValue := Module.End.Eigenvalues (scalarBaseResolvent g o d).toLinearMap

abbrev ScalarBaseSpectralSpace (μ : ScalarBaseSpectralValue g o d) :=
  Module.End.eigenspace (scalarBaseResolvent g o d).toLinearMap μ.val

abbrev ScalarBaseEigenIndex :=
  Σ μ : ScalarBaseSpectralValue g o d, Fin (Module.finrank ℝ (ScalarBaseSpectralSpace g o d μ))

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

def scalarBaseHeatRate (μ : ScalarBaseEigenIndex g o d) : ℝ :=
  μ.1.val⁻¹ - 1

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

theorem fourHeatCoefficient_center (m : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ) (c U : FourSpace → ℝ)
    (hU0 : U 0 ≠ 0) :
    (m + 1 : ℝ) * fourHeatCoefficient a b c U (m + 1) 0 =
      -fourHeatLocalOperator (a 0) (b 0) (c 0) (fourHeatCoefficient a b c U m) 0 := by
  simp only [fourHeatCoefficient, fourHeatWeightedRadialAverage, fourHeatRadialAverage_zero]
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity of the local heat operator on actual twice differentiable
functions. These formulas allow cancellation in the finite heat ansatz. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeat_second_add (u v : FourSpace → ℝ) (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (x : FourSpace) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun y => u y + v y) i) j x =
      partialDeriv (partialDeriv u i) j x + partialDeriv (partialDeriv v i) j x := by
  have he : partialDeriv (fun y => u y + v y) i =
      fun y => partialDeriv u i y + partialDeriv v i y := by
    funext y
    exact fourHeat_partial_add u v y (hu.differentiable (by norm_num)).differentiableAt
      (hv.differentiable (by norm_num)).differentiableAt i
  rw [he]
  exact fourHeat_partial_add _ _ x
    ((fourHeat_partial_contDiff 1 u hu i).differentiable one_ne_zero).differentiableAt
    ((fourHeat_partial_contDiff 1 v hv i).differentiable one_ne_zero).differentiableAt j

theorem fourHeatLocalOperator_add (a : Mat4) (b : Fin 4 → ℝ) (c : ℝ)
    (u v : FourSpace → ℝ) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (x : FourSpace) :
    fourHeatLocalOperator a b c (fun y => u y + v y) x =
      fourHeatLocalOperator a b c u x + fourHeatLocalOperator a b c v x := by
  unfold fourHeatLocalOperator
  simp only [fourHeat_second_add u v hu hv,
    fourHeat_partial_add u v x (hu.differentiable (by norm_num)).differentiableAt
      (hv.differentiable (by norm_num)).differentiableAt,
    mul_add, Finset.sum_add_distrib]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of the coordinate Hessian contraction with the
actual framed rough trace of a smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heat_framedSecond_chart {g : SmoothMetric M} {o : FrameOrientation g}
    {u : M → TwoFormFour} (hu : TwoFormSmooth o u) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    twoFormFramedSecondDerivative o u e = frameTensor (frameChartMatrix g c e)
      (twoFormSecondCovariantCoordinates o u c (chartAt FourSpace c e.base)) := by
  have hb := mem_chart_source FourSpace e.base
  have ht := hu.secondCovariant_transition e.base c
    (chartAt FourSpace e.base e.base) ((chartAt FourSpace e.base).map_source hb)
    (by simpa only [(chartAt FourSpace e.base).left_inv hb] using he)
  have hz : chartTransition e.base c (chartAt FourSpace e.base e.base) =
      chartAt FourSpace c e.base := by
    change chartAt FourSpace c ((chartAt FourSpace e.base).symm
      (chartAt FourSpace e.base e.base)) = _
    rw [(chartAt FourSpace e.base).left_inv hb]
  rw [hz] at ht
  rw [frameChartMatrix_eq, frameTensor_mul, ← ht]
  rfl

variable [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.roughTrace_as_actual {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (x : FourSpace) (hx : x ∈ ball 0 D.radius) :
    twoFormFramedRoughTrace o u (D.frame x hx) =
      frameTensor (D.point x).2 (twoFormSecondTrace (metricInChart g c (D.point x).1)⁻¹
        (twoFormSecondCovariantCoordinates o u c (D.point x).1)) := by
  have hsource : (D.frame x hx).base ∈ (chartAt FourSpace c).source :=
    (chartAt FourSpace c).map_target (D.in_chart x hx)
  have h := heat_framedSecond_chart hu c (D.frame x hx) hsource
  have hm : frameChartMatrix g c (D.frame x hx) = (D.point x).2 :=
    frameChartMatrix_chartFrameState g c
      ⟨D.point x, D.in_chart x hx, D.orthonormal x hx⟩
  have hb : chartAt FourSpace c (D.frame x hx).base = (D.point x).1 :=
    (chartAt FourSpace c).right_inv (D.in_chart x hx)
  rw [hm, hb] at h
  funext v
  change (∑ i, twoFormFramedSecondDerivative o u (D.frame x hx)
    (Fin.cons i (Fin.cons i v))) = _
  rw [h, twoFormSecondTrace_frame, heat_orthonormal_inverse _ _ (D.orthonormal x hx)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration by parts at the finite regularity of the compact heat
parametrix. Only the coefficients near the actual compact support matter. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped ContDiff _root_.Topology

noncomputable section

theorem fourHeat_local_product_integrable (f q : FourSpace → ℝ)
    (hq : Continuous q) (hc : HasCompactSupport q)
    (hf : ∀ x ∈ tsupport q, ContinuousAt f x) :
    Integrable (fun x => f x * q x) := by
  have hs : tsupport (fun x => f x * q x) ⊆ tsupport q := tsupport_mul_subset_right
  have hp : Continuous (fun x => f x * q x) := by
    apply continuous_of_tsupport
    intro x hx
    exact (hf x (hs hx)).mul hq.continuousAt
  exact hp.integrable_of_hasCompactSupport hc.mul_left

theorem fourHeat_local_integration_by_parts (f u : FourSpace → ℝ)
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    (hf : ∀ x ∈ tsupport u, ContDiffAt ℝ 1 f x) (i : Fin 4) :
    (∫ x, f x * partialDeriv u i x) = -(∫ x, partialDeriv f i x * u x) := by
  have hDu : ContDiff ℝ 0 (partialDeriv u i) :=
    (hu.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const
  have hs : tsupport (partialDeriv u i) ⊆ tsupport u :=
    tsupport_fderiv_apply_subset ℝ (coordinateVector i)
  have hcD : HasCompactSupport (partialDeriv u i) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hs
  have hDf : Integrable (fun x => partialDeriv f i x * u x) := by
    apply fourHeat_local_product_integrable _ u hu.continuous hc
    intro x hx
    exact (((hf x hx).fderiv_right (m := 0) (by norm_num)).clm_apply
      contDiffAt_const).continuousAt
  have hfD : Integrable (fun x => f x * partialDeriv u i x) :=
    fourHeat_local_product_integrable f _ hDu.continuous hcD
      (fun x hx => (hf x (hs hx)).continuousAt)
  have hfu : Integrable (fun x => f x * u x) :=
    fourHeat_local_product_integrable f u hu.continuous hc
      (fun x hx => (hf x hx).continuousAt)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hDf hfD hfu
    (fun x hx => (hf x hx).differentiableAt one_ne_zero)
    (fun x _ => hu.differentiable one_ne_zero x)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite third-order scalar heat ansatz and its exact differential
identities. The coefficients here are actual scalar functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff

noncomputable section

theorem fourHeatPolynomial_hasDerivAt (u : Fin 4 → FourSpace → ℝ) (t : ℝ)
    (x : FourSpace) : HasDerivAt (fun s => fourHeatPolynomial u s x)
      (u 1 x + 2 * t * u 2 x + 3 * t ^ 2 * u 3 x) t := by
  have h := (((hasDerivAt_const t (u 0 x)).add ((hasDerivAt_id t).mul_const (u 1 x))).add
    (((hasDerivAt_id t).pow 2).mul_const (u 2 x))).add
      (((hasDerivAt_id t).pow 3).mul_const (u 3 x))
  refine h.congr_deriv ?_
  · norm_num

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial gauge forces the connection and its diagonal derivatives
to vanish at the center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_radial_axis_zero (f : FourSpace → ℝ) (i : Fin 4)
    (hf : ContinuousAt f 0)
    (h : ∀ᶠ t : ℝ in 𝓝 0, t * f (t • coordinateVector i) = 0) :
    (fun t : ℝ => f (t • coordinateVector i)) =ᶠ[𝓝 0] fun _ => 0 := by
  have hc : ContinuousAt (fun t : ℝ => f (t • coordinateVector i)) 0 := by
    have hc : ContinuousAt (fun t : ℝ => t • coordinateVector i) 0 :=
      (continuous_id.smul continuous_const).continuousAt
    have ht : Tendsto (fun t : ℝ => t • coordinateVector i) (𝓝 0) (𝓝 (0 : FourSpace)) := by
      simpa only [zero_smul] using hc.tendsto
    change Tendsto (fun t : ℝ => f (t • coordinateVector i)) (𝓝 0)
      (𝓝 (f ((0 : ℝ) • coordinateVector i)))
    simpa only [Function.comp_def, zero_smul] using hf.tendsto.comp ht
  have hne : (fun t : ℝ => f (t • coordinateVector i)) =ᶠ[𝓝[≠] 0] fun _ => 0 := by
    filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht hn
    exact (mul_eq_zero.mp ht).resolve_left hn
  have hlim : Tendsto (fun t : ℝ => f (t • coordinateVector i)) (𝓝[≠] 0) (𝓝 (f 0)) := by
    simpa only [zero_smul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hz : f 0 = 0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hne.symm)
  filter_upwards [h] with t ht
  by_cases htz : t = 0
  · simpa only [htz, zero_smul] using hz
  · exact (mul_eq_zero.mp ht).resolve_left htz

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact smooth cutoffs equal to one on a prescribed compact set
inside an open chart neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem exists_scalar_compact_cutoff {K U : Set FourSpace} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : FourSpace → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨V, hV, hKV, hVU, hcV⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  have hKi : K ⊆ interior V := by simpa only [hV.interior_eq] using hKV
  obtain ⟨χ, hone, hzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := I4) (n := (⊤ : ℕ∞)) hK.isClosed hKi
  have hsupport : tsupport (χ : FourSpace → ℝ) ⊆ closure V := by
    apply closure_minimal
    · intro x hx
      by_contra hxV
      exact hx (hzero x (fun hx => hxV (subset_closure hx)))
    · exact isClosed_closure
  refine ⟨χ, χ.contMDiff.contDiff, hcV.of_isClosed_subset (isClosed_tsupport _) hsupport,
    hsupport.trans hVU, ?_⟩
  intro x hx
  exact hone.self_of_nhdsSet x hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Successive matrix heat amplitudes are actual radial integrals of the
preceding amplitude under the six-component differential operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatBundleCoefficient_center (m : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → HeatMat6) (C : FourSpace → HeatMat6) (U : FourSpace → ℝ)
    (hU0 : U 0 ≠ 0) (k l : Fin 6) :
    (m + 1 : ℝ) * fourHeatBundleCoefficient a b B C U (m + 1) 0 k l =
      -fourHeatBundleOperator (a 0) (b 0) (B 0) (C 0)
        (fun y q => fourHeatBundleCoefficient a b B C U m y q l) 0 k := by
  simp only [fourHeatBundleCoefficient, fourHeatWeightedRadialAverage, fourHeatRadialAverage_zero]
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  field_simp

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

theorem fourHeatBundleOperator_add (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) (u v : FourSpace → Fin 6 → ℝ)
    (hu : ∀ l, ContDiff ℝ 2 (fun x => u x l))
    (hv : ∀ l, ContDiff ℝ 2 (fun x => v x l)) (x : FourSpace) (k : Fin 6) :
    fourHeatBundleOperator a b B C (fun y l => u y l + v y l) x k =
      fourHeatBundleOperator a b B C u x k + fourHeatBundleOperator a b B C v x k := by
  unfold fourHeatBundleOperator fourHeatBundleFirst fourHeatBundleZero
  rw [fourHeatLocalOperator_add a b 0 _ _ (hu k) (hv k)]
  have hp (i : Fin 4) (l : Fin 6) :
      partialDeriv (fun y => u y l + v y l) i x =
      partialDeriv (fun y => u y l) i x + partialDeriv (fun y => v y l) i x :=
    fourHeat_partial_add _ _ x ((hu l).differentiable (by norm_num)).differentiableAt
      ((hv l).differentiable (by norm_num)).differentiableAt i
  simp only [hp, mul_add, Finset.sum_add_distrib]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! A bounded continuous time-dependent amplitude is sampled at the
origin by the actual Gaussian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology

noncomputable section

theorem fourHeatGaussian_family_limit (F : ℝ → FourSpace → ℝ)
    (hF : Continuous (fun z : ℝ × FourSpace => F z.1 z.2))
    (B T : ℝ) (hT : 0 < T) (hB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖F t x‖ ≤ B) :
    Tendsto (fun t => ∫ x : FourSpace, fourHeatGaussian t x * F t x)
      (𝓝[>] 0) (𝓝 (F 0 0)) := by
  have hpoint (z : FourSpace) :
      Tendsto (fun t : ℝ => fourHeatGaussian 1 z * F t (Real.sqrt t • z))
        (𝓝[>] 0) (𝓝 (fourHeatGaussian 1 z * F 0 0)) := by
    have hs : Tendsto (fun t : ℝ => Real.sqrt t • z) (𝓝 0) (𝓝 (0 : FourSpace)) := by
      simpa only [Real.sqrt_zero, zero_smul] using
        ((Real.continuous_sqrt.tendsto 0).smul
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => z) (𝓝 0) (𝓝 z)))
    have ha : Tendsto (fun t : ℝ => (t, Real.sqrt t • z)) (𝓝 0) (𝓝 (0, (0 : FourSpace))) :=
      tendsto_id.prodMk_nhds hs
    exact ((tendsto_const_nhds : Tendsto (fun _ : ℝ => fourHeatGaussian 1 z) (𝓝 0)
      (𝓝 (fourHeatGaussian 1 z))).mul ((hF.tendsto _).comp ha)).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Icc (0 : ℝ) T := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds]
      with t ht htT
    exact ⟨ht.le, htT.le⟩
  have hbound : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ z : FourSpace,
      ‖fourHeatGaussian 1 z * F t (Real.sqrt t • z)‖ ≤ fourHeatGaussian 1 z * B := by
    filter_upwards [hsmall] with t ht
    exact Eventually.of_forall fun z => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (fourHeatGaussian_pos 1 zero_lt_one z)]
      exact mul_le_mul_of_nonneg_left (hB t ht _) (fourHeatGaussian_pos 1 zero_lt_one z).le
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun z : FourSpace => fourHeatGaussian 1 z * F t (Real.sqrt t • z)) volume := by
    apply Continuous.aestronglyMeasurable
    apply (fourHeatGaussian_continuous 1).mul
    exact hF.comp ((continuous_const : Continuous (fun _ : FourSpace => t)).prodMk
      ((continuous_const : Continuous (fun _ : FourSpace => Real.sqrt t)).smul continuous_id))
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure FourSpace)) (l := 𝓝[>] (0 : ℝ))
    (F := fun t z => fourHeatGaussian 1 z * F t (Real.sqrt t • z))
    (f := fun z => fourHeatGaussian 1 z * F 0 0)
    (fun z => fourHeatGaussian 1 z * B) (Eventually.of_forall hmeas) hbound
    ((fourHeatGaussian_integrable 1 zero_lt_one).mul_const B) (Eventually.of_forall hpoint)
  simp only [integral_mul_const, fourHeatGaussian_mass 1 zero_lt_one, one_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have h := fourHeatGaussian_integral_dilate t ht (fun x => F t (-x)) 0
  simpa only [zero_sub, neg_neg] using h.symm

theorem fourHeatGaussian_square_half (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    t ^ 2 * fourHeatGaussian t x ^ 2 =
      (1 / (64 * Real.pi ^ 2)) * fourHeatGaussian (t / 2) x := by
  have he : 2 * (-(4 * t)⁻¹ * ‖x‖ ^ 2) = -(4 * (t / 2))⁻¹ * ‖x‖ ^ 2 := by
    field_simp
  unfold fourHeatGaussian
  rw [mul_pow, ← Real.exp_nat_mul, show (2 : ℕ) = 2 from rfl, Nat.cast_ofNat, he]
  field_simp [Real.pi_ne_zero]
  ring

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

def fourHeatPolynomialTime (u : Fin 4 → FourSpace → ℝ) (t : ℝ) (x : FourSpace) : ℝ :=
  u 1 x + 2 * t * u 2 x + 3 * t ^ 2 * u 3 x

def fourHeatGaussianPolynomialTime (u : Fin 4 → FourSpace → ℝ) (t : ℝ) (x : FourSpace) : ℝ :=
  (fourHeatGaussianTimeFactor t x * fourHeatGaussian t x) * fourHeatPolynomial u t x +
    fourHeatGaussian t x * fourHeatPolynomialTime u t x

theorem fourHeatGaussianPolynomial_hasDerivAt (u : Fin 4 → FourSpace → ℝ)
    (t : ℝ) (ht : 0 < t) (x : FourSpace) :
    HasDerivAt (fun s => fourHeatGaussian s x * fourHeatPolynomial u s x)
      (fourHeatGaussianPolynomialTime u t x) t :=
  (fourHeatGaussian_hasDerivAt_time t ht x).mul (fourHeatPolynomial_hasDerivAt u t x)

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

theorem HeatNormalFrameData.frame_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (he : e.base ∈ (chartAt FourSpace c).source) :
    D.frame 0 (mem_ball_self D.radius_pos) = e := by
  unfold HeatNormalFrameData.frame
  simpa only [D.initial, frameCoordinateState] using chartFrameStateToBundle_fromFrame g c e he

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

theorem heat_partial_coordinate (k i : Fin 4) (x : FourSpace) :
    partialDeriv (fun y : FourSpace => y k) i x = if i = k then 1 else 0 := by
  change (fderiv ℝ (EuclideanSpace.proj k) x) (coordinateVector i) = _
  rw [(EuclideanSpace.proj k : FourSpace →L[ℝ] ℝ).hasFDerivAt.fderiv]
  simp [coordinateVector, PiLp.single_apply, eq_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coordinate product rule for two successive covariant derivatives
of six-component fields. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def fourHeatCovariantDerivative (A : Fin 4 → FourSpace → HeatMat6)
    (u : FourSpace → Fin 6 → ℝ) (i : Fin 4) (x : FourSpace) (k : Fin 6) : ℝ :=
  partialDeriv (fun y => u y k) i x + ∑ l : Fin 6, A i x k l * u x l

theorem fourHeat_partial_sum_six (f : Fin 6 → FourSpace → ℝ) (x : FourSpace)
    (hf : ∀ l, DifferentiableAt ℝ (f l) x) (i : Fin 4) :
    partialDeriv (fun y => ∑ l : Fin 6, f l y) i x =
      ∑ l : Fin 6, partialDeriv (f l) i x := by
  unfold partialDeriv
  rw [fderiv_fun_sum (u := Finset.univ) (A := f) (fun l _ => hf l), _root_.sum_apply]

theorem fourHeatCovariantDerivative_partial (A : Fin 4 → FourSpace → HeatMat6)
    (u : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (hA : ∀ i k l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (i j : Fin 4) (k : Fin 6) :
    partialDeriv (fun y => fourHeatCovariantDerivative A u i y k) j x =
      partialDeriv (partialDeriv (fun y => u y k) i) j x +
        (∑ l : Fin 6, partialDeriv (fun y => A i y k l) j x * u x l) +
        ∑ l : Fin 6, A i x k l * partialDeriv (fun y => u y l) j x := by
  have hu0 (l : Fin 6) : DifferentiableAt ℝ (fun y => u y l) x :=
    (hu l).differentiableAt (by norm_num)
  have hdu : DifferentiableAt ℝ (partialDeriv (fun y => u y k) i) x :=
    (((hu k).fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := coordinateVector i))).differentiableAt one_ne_zero
  have hprod (l : Fin 6) : DifferentiableAt ℝ (fun y => A i y k l * u y l) x :=
    (hA i k l).mul (hu0 l)
  have hsum : DifferentiableAt ℝ (fun y => ∑ l : Fin 6, A i y k l * u y l) x :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun l _ => hprod l)
  unfold fourHeatCovariantDerivative
  rw [fourHeat_partial_add (partialDeriv (fun y => u y k) i)
    (fun y => ∑ l : Fin 6, A i y k l * u y l) x hdu hsum j,
    fourHeat_partial_sum_six (fun l y => A i y k l * u y l) x hprod j]
  simp only [scalar_partial_product _ _ x (hA i k _) (hu0 _) j, Finset.sum_add_distrib]
  ring

theorem fourHeatCovariantDerivative_second (A : Fin 4 → FourSpace → HeatMat6)
    (u : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (hA : ∀ i k l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (i j : Fin 4) (k : Fin 6) :
    fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u i) j x k =
      partialDeriv (partialDeriv (fun y => u y k) i) j x +
        (∑ l : Fin 6, A i x k l * partialDeriv (fun y => u y l) j x) +
        (∑ l : Fin 6, A j x k l * partialDeriv (fun y => u y l) i x) +
        ∑ l : Fin 6, (partialDeriv (fun y => A i y k l) j x +
          (A j x * A i x) k l) * u x l := by
  change partialDeriv (fun y => fourHeatCovariantDerivative A u i y k) j x +
    (∑ l : Fin 6, A j x k l * fourHeatCovariantDerivative A u i x l) = _
  rw [fourHeatCovariantDerivative_partial A u x hA hu]
  have hquad : (∑ l : Fin 6, A j x k l * ∑ q : Fin 6, A i x l q * u x q) =
      ∑ q : Fin 6, (A j x * A i x) k q * u x q := by
    simp only [Finset.mul_sum, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp only [fourHeatCovariantDerivative, mul_add, Finset.sum_add_distrib]
  rw [hquad]
  simp only [add_mul, Finset.sum_add_distrib]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact second moments of the actual four-dimensional heat Gaussian.
The normalization is obtained by integration by parts against coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators

noncomputable section

theorem fourHeatGaussian_quadratic_majorant_integrable (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : FourSpace => (‖x‖ ^ 2 + 1) * fourHeatGaussian t x) := by
  convert (fourHeatGaussian_moment_integrable 1 t ht).add
    (fourHeatGaussian_integrable t ht) using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  norm_num
  ring

theorem fourHeatGaussian_coordinate_integrable (t : ℝ) (ht : 0 < t) (i : Fin 4) :
    Integrable (fun x : FourSpace => x i * fourHeatGaussian t x) := by
  apply (fourHeatGaussian_quadratic_majorant_integrable t ht).mono'
  · exact ((EuclideanSpace.proj i : FourSpace →L[ℝ] ℝ).continuous.mul
      (fourHeatGaussian_continuous t)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_of_nonneg (fourHeatGaussian_pos t ht x).le]
      apply mul_le_mul_of_nonneg_right _ (fourHeatGaussian_pos t ht x).le
      have h := PiLp.norm_apply_le x i
      nlinarith [norm_nonneg x, sq_nonneg (‖x‖ - 1)]

theorem fourHeatGaussian_coordinate_pair_integrable (t : ℝ) (ht : 0 < t) (i j : Fin 4) :
    Integrable (fun x : FourSpace => x i * x j * fourHeatGaussian t x) := by
  apply (fourHeatGaussian_quadratic_majorant_integrable t ht).mono'
  · exact (((EuclideanSpace.proj i : FourSpace →L[ℝ] ℝ).continuous.mul
      (EuclideanSpace.proj j : FourSpace →L[ℝ] ℝ).continuous).mul
      (fourHeatGaussian_continuous t)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (fourHeatGaussian_pos t ht x).le]
      apply mul_le_mul_of_nonneg_right _ (fourHeatGaussian_pos t ht x).le
      have h := mul_le_mul (PiLp.norm_apply_le x i) (PiLp.norm_apply_le x j)
        (norm_nonneg (x j)) (norm_nonneg x)
      nlinarith

theorem fourHeatGaussian_coordinate_covariance (t : ℝ) (ht : 0 < t) (i j : Fin 4) :
    (∫ x : FourSpace, x i * x j * fourHeatGaussian t x) =
      2 * t * (if i = j then 1 else 0) := by
  have hleft : Integrable (fun x : FourSpace =>
      partialDeriv (fun y : FourSpace => y j) i x * fourHeatGaussian t x) := by
    simpa only [heat_partial_coordinate] using
      (fourHeatGaussian_integrable t ht).const_mul (if i = j then (1 : ℝ) else 0)
  have hright : Integrable (fun x : FourSpace =>
      x j * partialDeriv (fourHeatGaussian t) i x) := by
    have hi := (fourHeatGaussian_coordinate_pair_integrable t ht i j).const_mul (-(2 * t)⁻¹)
    convert hi using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    rw [fourHeatGaussian_partial t ht.ne' i x]
    ring
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := coordinateVector i) hleft hright (fourHeatGaussian_coordinate_integrable t ht j)
    (fun x _ => (fourHeatGaussian_coordinate_hasFDerivAt j x).differentiableAt)
    (fun x _ => (fourHeatGaussian_hasFDerivAt t x).differentiableAt)
  change (∫ x : FourSpace, x j * partialDeriv (fourHeatGaussian t) i x) =
    -(∫ x : FourSpace, partialDeriv (fun y : FourSpace => y j) i x * fourHeatGaussian t x) at h
  have heq : (fun x : FourSpace => x j * partialDeriv (fourHeatGaussian t) i x) =
      fun x => (-(2 * t)⁻¹) * (x i * x j * fourHeatGaussian t x) := by
    funext x
    rw [fourHeatGaussian_partial t ht.ne' i x]
    ring
  rw [heq, integral_const_mul] at h
  simp only [heat_partial_coordinate, integral_const_mul, fourHeatGaussian_mass t ht, mul_one] at h
  field_simp [ht.ne'] at h
  linarith

theorem fourHeatGaussian_hessian_integral (t : ℝ) (ht : 0 < t) (A : Mat4) :
    (∫ x : FourSpace, (∑ i, ∑ j, A i j * x i * x j) * fourHeatGaussian t x) =
      2 * t * A.trace := by
  have hi (i j : Fin 4) : Integrable (fun x : FourSpace =>
      A i j * (x i * x j * fourHeatGaussian t x)) :=
    (fourHeatGaussian_coordinate_pair_integrable t ht i j).const_mul _
  have heq : (fun x : FourSpace => (∑ i, ∑ j, A i j * x i * x j) * fourHeatGaussian t x) =
      fun x => ∑ i, ∑ j, A i j * (x i * x j * fourHeatGaussian t x) := by
    funext x
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j), integral_const_mul,
    fourHeatGaussian_coordinate_covariance t ht]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, if_true]
  simp only [Matrix.trace, Matrix.diag, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact rescaling and the leading limit for squared Gaussian integrals. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology

noncomputable section

theorem fourHeatGaussian_square_weighted (F : FourSpace → ℝ) (t : ℝ) (ht : 0 < t) :
    t ^ 2 * (∫ x, fourHeatGaussian t x ^ 2 * F x) =
      (1 / (64 * Real.pi ^ 2)) * ∫ x, fourHeatGaussian (t / 2) x * F x := by
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change t ^ 2 * (fourHeatGaussian t x ^ 2 * F x) = _
    rw [← mul_assoc, fourHeatGaussian_square_half t ht]
    ring

theorem fourHeatGaussian_square_family_limit (F : ℝ → FourSpace → ℝ)
    (hF : Continuous (fun z : ℝ × FourSpace => F z.1 z.2))
    (B T : ℝ) (hT : 0 < T) (hB : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, ‖F t x‖ ≤ B) :
    Tendsto (fun t => t ^ 2 * ∫ x, fourHeatGaussian t x ^ 2 * F t x)
      (𝓝[>] 0) (𝓝 ((1 / (64 * Real.pi ^ 2)) * F 0 0)) := by
  let H := fun s x => F (2 * s) x
  have hH : Continuous (fun z : ℝ × FourSpace => H z.1 z.2) :=
    hF.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd)
  have hb : ∀ s ∈ Icc (0 : ℝ) (T / 2), ∀ x, ‖H s x‖ ≤ B := by
    intro s hs x
    exact hB (2 * s) ⟨by linarith [hs.1], by linarith [hs.2]⟩ x
  have hhalf : Tendsto (fun t : ℝ => t / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hi : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [zero_div] using hi.div_const (2 : ℝ)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      show (0 : ℝ) < t / 2
      exact half_pos ht
  have hlim := (fourHeatGaussian_family_limit H hH B (T / 2) (half_pos hT) hb).comp hhalf
  have hlim' : Tendsto (fun t => ∫ x, fourHeatGaussian (t / 2) x * F t x)
      (𝓝[>] 0) (𝓝 (F 0 0)) := by
    change Tendsto (fun t => ∫ x, fourHeatGaussian (t / 2) x * F (2 * (t / 2)) x)
      (𝓝[>] 0) (𝓝 (F (2 * 0) 0)) at hlim
    have he (t : ℝ) : 2 * (t / 2) = t := by ring
    simpa only [he, mul_zero] using hlim
  apply (tendsto_const_nhds.mul hlim').congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (fourHeatGaussian_square_weighted (F t) t ht).symm

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

theorem HeatNormalBundleExtension.amplitude_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalBundleExtension D) (x : FourSpace) :
    E.amplitude 0 x = E.base.U x • (1 : HeatMat6) := by
  ext k l
  simp only [HeatNormalBundleExtension.amplitude, fourHeatBundleCoefficient,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]

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

theorem HeatNormalFrameData.frame_connection_zero (D : HeatNormalFrameData g o c e)
    (i : Fin 4) : heatNormalFrameConnection g c D.point i 0 = 0 := by
  ext k l
  have hR : ∀ᶠ x in 𝓝 (0 : FourSpace),
      (∑ j, x j • heatNormalFrameConnection g c D.point j x) = 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : FourSpace) D.radius_pos] with x hx
    exact D.radial_connection x hx
  have ht : Tendsto (fun t : ℝ => t • coordinateVector i) (𝓝 0) (𝓝 (0 : FourSpace)) := by
    have hc : ContinuousAt (fun t : ℝ => t • coordinateVector i) 0 :=
      (continuous_id.smul continuous_const).continuousAt
    simpa only [zero_smul] using hc.tendsto
  have ha := heat_radial_axis_zero
    (fun x => heatNormalFrameConnection g c D.point i x k l) i
    (D.connection_regular i k l).continuousAt (by
      filter_upwards [ht.eventually hR] with t h
      have hh := congrArg (fun B : Mat4 => B k l) h
      simpa [coordinateVector, PiLp.single_apply, PiLp.smul_apply] using hh)
  simpa only [zero_smul, Matrix.zero_apply] using ha.self_of_nhds

end
end PositiveEinsteinFour.Geometry
end


section

/-! Expansion of the connection Laplacian into the exact coefficient
operator used in the bundle heat construction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

def fourHeatCovariantOperator (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6)
    (u : FourSpace → Fin 6 → ℝ) (x : FourSpace) (k : Fin 6) : ℝ :=
  -(∑ i : Fin 4, ∑ j : Fin 4, a i j *
      fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u i) j x k) +
    (∑ i : Fin 4, b i * fourHeatCovariantDerivative A u i x k) +
    ∑ l : Fin 6, V k l * u x l

theorem fourHeatCovariantOperator_eq (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6)
    (u : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (hs : ∀ i j, a i j = a j i)
    (hA : ∀ i k l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (k : Fin 6) :
    fourHeatCovariantOperator a b A V u x k =
      fourHeatBundleOperator a b (fourHeatConnectionFirst a (fun i => A i x))
        (fourHeatConnectionZero a b A V x) u x k := by
  let Q := ∑ i : Fin 4, ∑ j : Fin 4, a i j *
    (∑ l : Fin 6, A j x k l * partialDeriv (fun y => u y l) i x)
  let Z := ∑ i : Fin 4, ∑ j : Fin 4, a i j *
    (∑ l : Fin 6, (partialDeriv (fun y => A i y k l) j x +
      (A j x * A i x) k l) * u x l)
  let Y := ∑ i : Fin 4, b i * (∑ l : Fin 6, A i x k l * u x l)
  have hswap : (∑ i : Fin 4, ∑ j : Fin 4, a i j *
      (∑ l : Fin 6, A i x k l * partialDeriv (fun y => u y l) j x)) = Q := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hs]
  have hsecond : (∑ i : Fin 4, ∑ j : Fin 4, a i j *
      fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u i) j x k) =
      (∑ i : Fin 4, ∑ j : Fin 4, a i j *
        partialDeriv (partialDeriv (fun y => u y k) i) j x) + 2 * Q + Z := by
    simp_rw [fourHeatCovariantDerivative_second A u x hA hu]
    simp only [mul_add, Finset.sum_add_distrib]
    rw [hswap]
    dsimp only [Q, Z]
    ring
  have hfirst : fourHeatBundleFirst (fourHeatConnectionFirst a (fun i => A i x)) u x k = -2 * Q := by
    change (∑ i : Fin 4, ∑ l : Fin 6,
      (-2 * ∑ j : Fin 4, a i j * A j x k l) * partialDeriv (fun y => u y l) i x) = _
    dsimp only [Q]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hY : (∑ l : Fin 6, (∑ i : Fin 4, b i * A i x k l) * u x l) = Y := by
    dsimp only [Y]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hZ : (∑ l : Fin 6, (∑ i : Fin 4, ∑ j : Fin 4, a i j *
      (partialDeriv (fun y => A i y k l) j x + (A j x * A i x) k l)) * u x l) = Z := by
    dsimp only [Z]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hzero : fourHeatBundleZero (fourHeatConnectionZero a b A V x) u x k =
      (∑ l : Fin 6, V k l * u x l) + Y - Z := by
    change (∑ l : Fin 6, (V k l + (∑ i : Fin 4, b i * A i x k l) -
      (∑ i : Fin 4, ∑ j : Fin 4, a i j *
        (partialDeriv (fun y => A i y k l) j x + (A j x * A i x) k l))) * u x l) = _
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hY, hZ]
  unfold fourHeatCovariantOperator fourHeatBundleOperator
  rw [hsecond, hfirst, hzero]
  simp only [fourHeatCovariantDerivative, mul_add, Finset.sum_add_distrib]
  dsimp only [Y]
  unfold fourHeatLocalOperator
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric product rule for the six-component skew connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatCovariantDerivative_pairing
    (A : Fin 4 → FourSpace → HeatMat6) (u v : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (i : Fin 4) (hA : (A i x)ᵀ = -A i x)
    (hu : ∀ k, DifferentiableAt ℝ (fun y => u y k) x)
    (hv : ∀ k, DifferentiableAt ℝ (fun y => v y k) x) :
    partialDeriv (fun y => ∑ k, u y k * v y k) i x =
      (∑ k, fourHeatCovariantDerivative A u i x k * v x k) +
        ∑ k, u x k * fourHeatCovariantDerivative A v i x k := by
  rw [fourHeat_partial_sum_six (fun k y => u y k * v y k) x
    (fun k => (hu k).mul (hv k)) i]
  change (∑ k, partialDeriv (fun y => u y k * v y k) i x) =
    (∑ k, (partialDeriv (fun y => u y k) i x + ∑ l, A i x k l * u x l) * v x k) +
      ∑ k, u x k * (partialDeriv (fun y => v y k) i x + ∑ l, A i x k l * v x l)
  have hd (k : Fin 6) := scalar_partial_product (fun y => u y k) (fun y => v y k)
    x (hu k) (hv k) i
  simp_rw [hd]
  simp only [Finset.sum_add_distrib, add_mul, mul_add]
  have hs := fourHeat_skew_pairing (A i x) hA (u x) (v x)
  linarith only [hs]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar product rule and the weighted divergence coefficient of
the six-component connection Laplacian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatCovariantDerivative_scalar
    (A : Fin 4 → FourSpace → HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (f : FourSpace → ℝ) (x : FourSpace) (i : Fin 4) (k : Fin 6)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ (fun y => u y k) x) :
    fourHeatCovariantDerivative A (fun y l => f y * u y l) i x k =
      partialDeriv f i x * u x k + f x * fourHeatCovariantDerivative A u i x k := by
  change partialDeriv (fun y => f y * u y k) i x +
    (∑ l, A i x k l * (f x * u x l)) = _
  rw [scalar_partial_product f (fun y => u y k) x hf hu i]
  have he : (∑ l, A i x k l * (f x * u x l)) =
      f x * ∑ l, A i x k l * u x l := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he]
  change _ = partialDeriv f i x * u x k +
    f x * (partialDeriv (fun y => u y k) i x + ∑ l, A i x k l * u x l)
  ring

theorem fourHeatDensityDrift_weighted (a : FourSpace → Mat4) (ρ : FourSpace → ℝ)
    (x : FourSpace) (j : Fin 4) (hρ : DifferentiableAt ℝ ρ x) (hρ0 : ρ x ≠ 0)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i j) x) :
    ρ x * fourHeatDensityDrift a ρ x j =
      -(∑ i, partialDeriv (fun y => ρ y * a y i j) i x) := by
  have hp (i : Fin 4) := scalar_partial_product ρ (fun y => a y i j) x hρ (ha i) i
  change ρ x * -((∑ i, partialDeriv (fun y => a y i j) i x) +
    (ρ x)⁻¹ * ∑ i, a x i j * partialDeriv ρ i x) = _
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs : (∑ i, partialDeriv ρ i x * a x i j) =
      ∑ i, a x i j * partialDeriv ρ i x := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  field_simp
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.oneFirst_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (i : Fin 4) : heatNormalOneFirst D 0 i = 0 := by
  simp [heatNormalOneFirst, fourHeatOneConnectionFirst, D.frame_connection_zero]

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

/-! The actual density-weighted covariant flux and its first derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatCovariantDerivative_differentiable
    (A : Fin 4 → FourSpace → HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 6)
    (hA : ∀ l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    DifferentiableAt ℝ (fun y => fourHeatCovariantDerivative A u i y k) x := by
  apply DifferentiableAt.add
  · exact (((hu k).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt one_ne_zero
  · exact DifferentiableAt.fun_sum fun l _ =>
      (hA l).mul ((hu l).differentiableAt (by norm_num))

theorem fourHeatCovariantDerivative_sum_four
    (A : Fin 4 → FourSpace → HeatMat6) (w : Fin 4 → FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (j : Fin 4) (k : Fin 6)
    (hw : ∀ i, DifferentiableAt ℝ (fun y => w i y k) x) :
    fourHeatCovariantDerivative A (fun y l => ∑ i, w i y l) j x k =
      ∑ i, fourHeatCovariantDerivative A (w i) j x k := by
  have hd : partialDeriv (fun y => ∑ i, w i y k) j x =
      ∑ i, partialDeriv (fun y => w i y k) j x := by
    unfold partialDeriv
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun i y => w i y k) (fun i _ => hw i),
      _root_.sum_apply]
  change partialDeriv (fun y => ∑ i, w i y k) j x +
    (∑ l, A j x k l * ∑ i, w i x l) = _
  rw [hd]
  simp only [fourHeatCovariantDerivative, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun l i => A j x k l * w i x l)]

def fourHeatCovariantFlux (A : Fin 4 → FourSpace → HeatMat6)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ)
    (i : Fin 4) (x : FourSpace) (k : Fin 6) : ℝ :=
  ∑ j, (ρ x * a x i j) * fourHeatCovariantDerivative A u j x k

theorem fourHeatCovariantFlux_derivative
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (i j : Fin 4) (k : Fin 6)
    (hA : ∀ l q, DifferentiableAt ℝ (fun y => A l y k q) x)
    (ha : ∀ l, DifferentiableAt ℝ (fun y => a y i l) x)
    (hρ : DifferentiableAt ℝ ρ x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    fourHeatCovariantDerivative A (fourHeatCovariantFlux A a ρ u i) j x k =
      ∑ l, (partialDeriv (fun y => ρ y * a y i l) j x *
        fourHeatCovariantDerivative A u l x k +
        (ρ x * a x i l) * fourHeatCovariantDerivative A
          (fourHeatCovariantDerivative A u l) j x k) := by
  unfold fourHeatCovariantFlux
  rw [fourHeatCovariantDerivative_sum_four A _ x j k (fun l =>
    (hρ.mul (ha l)).mul (fourHeatCovariantDerivative_differentiable A u x l k (hA l) hu))]
  apply Finset.sum_congr rfl
  intro l _
  exact fourHeatCovariantDerivative_scalar A (fourHeatCovariantDerivative A u l)
    (fun y => ρ y * a y i l) x j k (hρ.mul (ha l))
    (fourHeatCovariantDerivative_differentiable A u x l k (hA l) hu)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity for the actual finite-regularity, skew connection.
The second section and connection need regularity only near the compact
support of the first section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeat_mul_contDiff_of_tsupport (n : ℕ) (u f : FourSpace → ℝ)
    (hu : ContDiff ℝ n u) (hf : ∀ x ∈ tsupport u, ContDiffAt ℝ n f x) :
    ContDiff ℝ n (fun x => u x * f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport u
  · exact hu.contDiffAt.mul (hf x hx)
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hx] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

theorem fourHeatCovariantDerivative_pairing_integrable
    (A : Fin 4 → FourSpace → HeatMat6) (u v : FourSpace → Fin 6 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, Continuous (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x) :
    Integrable (fun x => ∑ k, u x k * fourHeatCovariantDerivative A v i x k) := by
  apply integrable_finsetSum
  intro k _
  have hcv (x : FourSpace) (hx : x ∈ tsupport (fun y => u y k)) :
      ContinuousAt (fun y => fourHeatCovariantDerivative A v i y k) x := by
    have hxU := hs k hx
    apply ContinuousAt.add
    · exact (((hv x hxU k).fderiv_right (m := 0) (by norm_num)).clm_apply
        contDiffAt_const).continuousAt
    · exact tendsto_finsetSum _ fun l _ =>
        (hA x hxU k l).mul (hv x hxU l).continuousAt
  have hp := fourHeat_local_product_integrable _ _ (hu k) (hc k) hcv
  simpa only [mul_comm] using hp

theorem fourHeatCovariantDerivative_pairing_global
    (A : Fin 4 → FourSpace → HeatMat6) (u v : FourSpace → Fin 6 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) (x : FourSpace) :
    partialDeriv (fun y => ∑ k, u y k * v y k) i x =
      (∑ k, fourHeatCovariantDerivative A u i x k * v x k) +
        ∑ k, u x k * fourHeatCovariantDerivative A v i x k := by
  by_cases hx : x ∈ U
  · exact fourHeatCovariantDerivative_pairing A u v x i (hskew x hx)
      (fun k => (hu k).differentiable one_ne_zero x)
      (fun k => (hv x hx k).differentiableAt one_ne_zero)
  · have hz : ∀ᶠ y in 𝓝 x, ∀ k : Fin 6, u y k = 0 := by
      apply eventually_all.mpr
      intro k
      have hk : x ∉ tsupport (fun y => u y k) := fun hk => hx (hs k hk)
      filter_upwards [(isClosed_tsupport (fun y => u y k)).isOpen_compl.mem_nhds hk]
        with y hy
      exact image_eq_zero_of_notMem_tsupport (f := fun y => u y k) hy
    have hzF : (fun y => ∑ k : Fin 6, u y k * v y k) =ᶠ[𝓝 x] (fun _ => 0) :=
      hz.mono fun y hy => by simp [hy]
    have hFD : partialDeriv (fun y => ∑ k : Fin 6, u y k * v y k) i x = 0 := by
      unfold partialDeriv
      rw [hzF.fderiv_eq, fderiv_const_apply]
      rfl
    have hDu (k : Fin 6) : partialDeriv (fun y => u y k) i x = 0 := by
      have hek : (fun y => u y k) =ᶠ[𝓝 x] (fun _ => 0) := hz.mono fun y hy => hy k
      unfold partialDeriv
      rw [hek.fderiv_eq, fderiv_const_apply]
      rfl
    simp only [hFD, fourHeatCovariantDerivative, hz.self_of_nhds,
      hDu, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

theorem fourHeat_partial_integral_zero (F : FourSpace → ℝ)
    (hF : ContDiff ℝ 1 F) (hcF : HasCompactSupport F) (i : Fin 4) :
    (∫ x, partialDeriv F i x) = 0 := by
  have hz := fourHeat_local_integration_by_parts (fun _ => 1) F hF hcF
    (fun _ _ => contDiffAt_const) i
  simpa only [one_mul, partialDeriv, fderiv_const_apply, _root_.zero_apply,
    zero_mul, integral_zero, neg_zero] using hz

theorem fourHeat_green_of_pairing (F L R : FourSpace → ℝ) (i : Fin 4)
    (hF : ContDiff ℝ 1 F) (hcF : HasCompactSupport F) (hR : Integrable R)
    (hpoint : ∀ x, partialDeriv F i x = L x + R x) :
    (∫ x, L x) = -(∫ x, R x) := by
  have hDc : Continuous (partialDeriv F i) :=
    ((hF.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have hD : Integrable (partialDeriv F i) :=
    hDc.integrable_of_hasCompactSupport
      (hcF.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_fderiv_apply_subset ℝ (coordinateVector i)))
  have heq : L = fun x => partialDeriv F i x - R x := by
    funext x
    linarith only [hpoint x]
  rw [heq, integral_sub hD hR, fourHeat_partial_integral_zero F hF hcF i, zero_sub]

theorem fourHeat_pairing_contDiff (u v : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x) :
    ContDiff ℝ 1 (fun x => ∑ k, u x k * v x k) := by
  have hp (k : Fin 6) : ContDiff ℝ 1 (fun x => u x k * v x k) :=
    fourHeat_mul_contDiff_of_tsupport 1 (fun x => u x k) (fun x => v x k)
      (hu k) (fun x hx => hv x (hs k hx) k)
  exact ContDiff.sum fun k _ => hp k

theorem fourHeat_pairing_compact (u v : FourSpace → Fin 6 → ℝ)
    (hc : ∀ k, HasCompactSupport (fun x => u x k)) :
    HasCompactSupport (fun x => ∑ k, u x k * v x k) := by
  have hp (k : Fin 6) : HasCompactSupport (fun x => u x k * v x k) :=
    (hc k).mul_right
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (f := fun k x => u x k * v x k) (fun k _ => hp k)
  simpa only [Finset.sum_fn] using h

theorem fourHeatCovariantDerivative_green
    (A : Fin 4 → FourSpace → HeatMat6) (u v : FourSpace → Fin 6 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ k, fourHeatCovariantDerivative A u i x k * v x k) =
      -(∫ x, ∑ k, u x k * fourHeatCovariantDerivative A v i x k) := by
  exact fourHeat_green_of_pairing (fun x => ∑ k, u x k * v x k)
    (fun x => ∑ k, fourHeatCovariantDerivative A u i x k * v x k)
    (fun x => ∑ k, u x k * fourHeatCovariantDerivative A v i x k) i
    (fourHeat_pairing_contDiff u v U hu hs hv) (fourHeat_pairing_compact u v hc)
    (fourHeatCovariantDerivative_pairing_integrable A u v U i
      (fun k => (hu k).continuous) hc hs hv hA)
    (fourHeatCovariantDerivative_pairing_global A u v U i hu hs hv hskew)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Symmetry of the two finite contractions in the connection energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem fourHeat_metric_pairing_symm (a : Mat4)
    (ha : ∀ i j, a i j = a j i) (p q : Fin 4 → ℝ) :
    (∑ i, ∑ j, a i j * p i * q j) = ∑ i, ∑ j, a i j * q i * p j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ha j i]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The density-weighted connection Laplacian is the covariant
divergence of the actual metric flux. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatCovariantOperator_divergence
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (k : Fin 6)
    (hA : ∀ i l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hρ : DifferentiableAt ℝ ρ x) (hρ0 : ρ x ≠ 0)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x)
    (hsym : ∀ i j, a x i j = a x j i) :
    ρ x * fourHeatCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A V u x k =
      -(∑ i, fourHeatCovariantDerivative A (fourHeatCovariantFlux A a ρ u i) i x k) +
        ρ x * ∑ l, V k l * u x l := by
  let Q := ∑ i : Fin 4, ∑ j : Fin 4, a x i j *
    fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u i) j x k
  let B := ∑ i : Fin 4, fourHeatDensityDrift a ρ x i *
    fourHeatCovariantDerivative A u i x k
  have hb (i : Fin 4) :
      (∑ j, partialDeriv (fun y => ρ y * a y j i) j x) =
        -(ρ x * fourHeatDensityDrift a ρ x i) := by
    have h := fourHeatDensityDrift_weighted a ρ x i hρ hρ0 (fun j => ha j i)
    linarith only [h]
  have hfirst : (∑ i : Fin 4, ∑ j : Fin 4,
      partialDeriv (fun y => ρ y * a y i j) i x * fourHeatCovariantDerivative A u j x k) =
      -(ρ x * B) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hb]
    simp only [B, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsecond : (∑ i : Fin 4, ∑ j : Fin 4,
      (ρ x * a x i j) *
        fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u j) i x k) =
      ρ x * Q := by
    rw [Finset.sum_comm]
    simp only [Q, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
    ring
  have hflux (i : Fin 4) := fourHeatCovariantFlux_derivative A a ρ u x i i k
    hA (ha i) hρ hu
  have hdiv : (∑ i, fourHeatCovariantDerivative A (fourHeatCovariantFlux A a ρ u i) i x k) =
      ρ x * Q - ρ x * B := by
    simp_rw [hflux, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    ring
  rw [hdiv]
  change ρ x * (-Q + B + ∑ l, V k l * u x l) = _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity for a covariant divergence, with a compact test
section and coefficients regular only on its support. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeat_covariant_divergence_green
    (A : Fin 4 → FourSpace → HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (W : Fin 4 → FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hW : ∀ x ∈ U, ∀ i k, ContDiffAt ℝ 1 (fun y => W i y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ i : Fin 4, ∑ k : Fin 6,
      u x k * fourHeatCovariantDerivative A (W i) i x k) =
      -(∑ i : Fin 4, ∫ x, ∑ k : Fin 6, fourHeatCovariantDerivative A u i x k * W i x k) := by
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      u x k * fourHeatCovariantDerivative A (W i) i x k) :=
    fourHeatCovariantDerivative_pairing_integrable A u (W i) U i
      (fun k => (hu k).continuous) hc hs (fun x hx k => hW x hx i k)
      (fun x hx k l => hA x hx i k l)
  rw [integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := fourHeatCovariantDerivative_green A u (W i) U i hu hc hs
    (fun x hx k => hW x hx i k) (fun x hx k l => hA x hx i k l)
    (fun x hx => hskew x hx i)
  linarith only [h]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local regularity and compact support of the flux needed for the
second integration by parts. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeatCovariantDerivative_contDiffAt
    (A : Fin 4 → FourSpace → HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 6)
    (hA : ∀ l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    ContDiffAt ℝ 1 (fun y => fourHeatCovariantDerivative A u i y k) x := by
  apply ContDiffAt.add
  · exact ((hu k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  · exact ContDiffAt.sum fun l _ => (hA l).mul ((hu l).of_le (by norm_num))

theorem fourHeatCovariantFlux_contDiffAt
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 6)
    (hA : ∀ j l, ContDiffAt ℝ 1 (fun y => A j y k l) x)
    (ha : ∀ j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ContDiffAt ℝ 1 ρ x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    ContDiffAt ℝ 1 (fun y => fourHeatCovariantFlux A a ρ u i y k) x := by
  apply ContDiffAt.sum
  intro j _
  exact (hρ.mul (ha j)).mul (fourHeatCovariantDerivative_contDiffAt A u x j k (hA j) hu)

theorem fourHeatCovariantDerivative_support
    (A : Fin 4 → FourSpace → HeatMat6) (u : FourSpace → Fin 6 → ℝ)
    (i : Fin 4) (k : Fin 6) :
    tsupport (fun x => fourHeatCovariantDerivative A u i x k) ⊆
      ⋃ l : Fin 6, tsupport (fun x => u x l) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite fun l => isClosed_tsupport (fun x => u x l))
  intro x hx
  by_contra hn
  have hu (l : Fin 6) : x ∉ tsupport (fun y => u y l) :=
    fun h => hn (mem_iUnion.mpr ⟨l, h⟩)
  have hp : partialDeriv (fun y => u y k) i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hu k
      (tsupport_fderiv_apply_subset ℝ (coordinateVector i) h))
  have hz (l : Fin 6) : u x l = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => u y l) (hu l)
  apply hx
  simp only [fourHeatCovariantDerivative, hp, hz, mul_zero, Finset.sum_const_zero, zero_add]

theorem fourHeatCovariantFlux_support
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ) (i : Fin 4) (k : Fin 6) :
    tsupport (fun x => fourHeatCovariantFlux A a ρ u i x k) ⊆
      ⋃ l : Fin 6, tsupport (fun x => u x l) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite fun l => isClosed_tsupport (fun x => u x l))
  intro x hx
  by_contra hn
  have hz (j : Fin 4) : fourHeatCovariantDerivative A u j x k = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantDerivative A u j y k)
      (fun h => hn (fourHeatCovariantDerivative_support A u j k h))
  apply hx
  simp only [fourHeatCovariantFlux, hz, mul_zero, Finset.sum_const_zero]

theorem fourHeatCovariantFlux_compact
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ)
    (hc : ∀ k, HasCompactSupport (fun x => u x k)) (i : Fin 4) (k : Fin 6) :
    HasCompactSupport (fun x => fourHeatCovariantFlux A a ρ u i x k) :=
  (isCompact_iUnion hc).of_isClosed_subset (isClosed_tsupport _)
    (fourHeatCovariantFlux_support A a ρ u i k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second-order Gaussian limit, with the actual Euclidean normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology BigOperators

noncomputable section

theorem fourHeat_bilinear_coordinates (B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ)
    (x : FourSpace) :
    B x x = ∑ i, ∑ j, B (coordinateVector i) (coordinateVector j) * x i * x j := by
  have hx : (∑ i, x i • coordinateVector i) = x := sum_coordinateVector (WithLp.ofLp x)
  calc
    B x x = B (∑ i, x i • coordinateVector i) (∑ j, x j • coordinateVector j) := by
      rw [hx]
    _ = _ := by
      simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem fourHeatGaussian_bilinear_integral
    (B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ) :
    (∫ x : FourSpace, fourHeatGaussian 1 x * ((1 / 2 : ℝ) * B x x)) =
      ∑ i, B (coordinateVector i) (coordinateVector i) := by
  have h := fourHeatGaussian_hessian_integral 1 zero_lt_one
    (fun i j => B (coordinateVector i) (coordinateVector j))
  have he : (fun x : FourSpace => fourHeatGaussian 1 x * ((1 / 2 : ℝ) * B x x)) =
      fun x => (1 / 2 : ℝ) * ((∑ i, ∑ j,
        B (coordinateVector i) (coordinateVector j) * x i * x j) * fourHeatGaussian 1 x) := by
    funext x
    rw [fourHeat_bilinear_coordinates]
    ring
  rw [he, integral_const_mul, h]
  simp only [Matrix.trace, Matrix.diag]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The four-component covector specialization of the compact connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOne_skew_pairing (A : Mat4) (hA : Aᵀ = -A)
    (p q : Fin 4 → ℝ) :
    (∑ k, (∑ l, A k l * p l) * q k) =
      -(∑ k, p k * ∑ l, A k l * q l) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hs (k l : Fin 4) : A l k = -A k l := congrFun (congrFun hA k) l
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hs k l]
  ring

theorem fourHeatOneCovariantDerivative_pairing
    (A : Fin 4 → FourSpace → Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i : Fin 4) (hA : (A i x)ᵀ = -A i x)
    (hu : ∀ k, DifferentiableAt ℝ (fun y => u y k) x)
    (hv : ∀ k, DifferentiableAt ℝ (fun y => v y k) x) :
    partialDeriv (fun y => ∑ k, u y k * v y k) i x =
      (∑ k, fourHeatOneCovariantDerivative A u i x k * v x k) +
        ∑ k, u x k * fourHeatOneCovariantDerivative A v i x k := by
  rw [fourHeat_partial_sum_oneForm (fun k y => u y k * v y k) x
    (fun k => (hu k).mul (hv k)) i]
  change (∑ k, partialDeriv (fun y => u y k * v y k) i x) =
    (∑ k, (partialDeriv (fun y => u y k) i x + ∑ l, A i x k l * u x l) * v x k) +
      ∑ k, u x k * (partialDeriv (fun y => v y k) i x + ∑ l, A i x k l * v x l)
  have hd (k : Fin 4) := scalar_partial_product (fun y => u y k) (fun y => v y k)
    x (hu k) (hv k) i
  simp_rw [hd]
  simp only [Finset.sum_add_distrib, add_mul, mul_add]
  have hs := fourHeatOne_skew_pairing (A i x) hA (u x) (v x)
  linarith only [hs]

theorem fourHeatOneCovariantDerivative_pairing_integrable
    (A : Fin 4 → FourSpace → Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, Continuous (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x) :
    Integrable (fun x => ∑ k, u x k * fourHeatOneCovariantDerivative A v i x k) := by
  apply integrable_finsetSum
  intro k _
  have hcv (x : FourSpace) (hx : x ∈ tsupport (fun y => u y k)) :
      ContinuousAt (fun y => fourHeatOneCovariantDerivative A v i y k) x := by
    have hxU := hs k hx
    apply ContinuousAt.add
    · exact (((hv x hxU k).fderiv_right (m := 0) (by norm_num)).clm_apply
        contDiffAt_const).continuousAt
    · exact tendsto_finsetSum _ fun l _ =>
        (hA x hxU k l).mul (hv x hxU l).continuousAt
  have hp := fourHeat_local_product_integrable _ _ (hu k) (hc k) hcv
  simpa only [mul_comm] using hp

theorem fourHeatOneCovariantDerivative_pairing_global
    (A : Fin 4 → FourSpace → Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) (x : FourSpace) :
    partialDeriv (fun y => ∑ k, u y k * v y k) i x =
      (∑ k, fourHeatOneCovariantDerivative A u i x k * v x k) +
        ∑ k, u x k * fourHeatOneCovariantDerivative A v i x k := by
  by_cases hx : x ∈ U
  · exact fourHeatOneCovariantDerivative_pairing A u v x i (hskew x hx)
      (fun k => (hu k).differentiable one_ne_zero x)
      (fun k => (hv x hx k).differentiableAt one_ne_zero)
  · have hz : ∀ᶠ y in 𝓝 x, ∀ k : Fin 4, u y k = 0 := by
      apply eventually_all.mpr
      intro k
      have hk : x ∉ tsupport (fun y => u y k) := fun hk => hx (hs k hk)
      filter_upwards [(isClosed_tsupport (fun y => u y k)).isOpen_compl.mem_nhds hk]
        with y hy
      exact image_eq_zero_of_notMem_tsupport (f := fun y => u y k) hy
    have hzF : (fun y => ∑ k : Fin 4, u y k * v y k) =ᶠ[𝓝 x] (fun _ => 0) :=
      hz.mono fun y hy => by simp [hy]
    have hFD : partialDeriv (fun y => ∑ k : Fin 4, u y k * v y k) i x = 0 := by
      unfold partialDeriv
      rw [hzF.fderiv_eq, fderiv_const_apply]
      rfl
    have hDu (k : Fin 4) : partialDeriv (fun y => u y k) i x = 0 := by
      have hek : (fun y => u y k) =ᶠ[𝓝 x] (fun _ => 0) := hz.mono fun y hy => hy k
      unfold partialDeriv
      rw [hek.fderiv_eq, fderiv_const_apply]
      rfl
    simp only [hFD, fourHeatOneCovariantDerivative, hz.self_of_nhds,
      hDu, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]

theorem fourHeatOne_pairing_contDiff (u v : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x) :
    ContDiff ℝ 1 (fun x => ∑ k, u x k * v x k) := by
  have hp (k : Fin 4) : ContDiff ℝ 1 (fun x => u x k * v x k) :=
    fourHeat_mul_contDiff_of_tsupport 1 (fun x => u x k) (fun x => v x k)
      (hu k) (fun x hx => hv x (hs k hx) k)
  exact ContDiff.sum fun k _ => hp k

theorem fourHeatOne_pairing_compact (u v : FourSpace → Fin 4 → ℝ)
    (hc : ∀ k, HasCompactSupport (fun x => u x k)) :
    HasCompactSupport (fun x => ∑ k, u x k * v x k) := by
  have hp (k : Fin 4) : HasCompactSupport (fun x => u x k * v x k) :=
    (hc k).mul_right
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (f := fun k x => u x k * v x k) (fun k _ => hp k)
  simpa only [Finset.sum_fn] using h

theorem fourHeatOneCovariantDerivative_green
    (A : Fin 4 → FourSpace → Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ k, fourHeatOneCovariantDerivative A u i x k * v x k) =
      -(∫ x, ∑ k, u x k * fourHeatOneCovariantDerivative A v i x k) := by
  exact fourHeat_green_of_pairing (fun x => ∑ k, u x k * v x k)
    (fun x => ∑ k, fourHeatOneCovariantDerivative A u i x k * v x k)
    (fun x => ∑ k, u x k * fourHeatOneCovariantDerivative A v i x k) i
    (fourHeatOne_pairing_contDiff u v U hu hs hv) (fourHeatOne_pairing_compact u v hc)
    (fourHeatOneCovariantDerivative_pairing_integrable A u v U i
      (fun k => (hu k).continuous) hc hs hv hA)
    (fourHeatOneCovariantDerivative_pairing_global A u v U i hu hs hv hskew)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact amplitudes have globally C1 covariant fluxes even though the
normal coefficients are regular only inside the chosen chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped ContDiff _root_.Topology

noncomputable section

theorem fourHeatCovariantFlux_contDiff
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 2 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x) (i : Fin 4) (k : Fin 6) :
    ContDiff ℝ 1 (fun x => fourHeatCovariantFlux A a ρ u i x k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact fourHeatCovariantFlux_contDiffAt A a ρ u x i k (fun j l => hA x hx j k l)
      (ha x hx i) (hρ x hx) (fun l => (hu l).contDiffAt)
  · have hsub : tsupport (fun y => fourHeatCovariantFlux A a ρ u i y k) ⊆ U :=
      (fourHeatCovariantFlux_support A a ρ u i k).trans (iUnion_subset hs)
    have hn : x ∉ tsupport (fun y => fourHeatCovariantFlux A a ρ u i y k) :=
      fun hh => hx (hsub hh)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hN := (isClosed_tsupport (fun y => fourHeatCovariantFlux A a ρ u i y k)).isOpen_compl.mem_nhds hn
    filter_upwards [hN] with y hy
    exact image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantFlux A a ρ u i y k) hy

end
end PositiveEinsteinFour.Geometry
end


section

/-! The four-component covector specialization of the compact connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOneCovariantDerivative_differentiable
    (A : Fin 4 → FourSpace → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 4)
    (hA : ∀ l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    DifferentiableAt ℝ (fun y => fourHeatOneCovariantDerivative A u i y k) x := by
  apply DifferentiableAt.add
  · exact (((hu k).fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const).differentiableAt one_ne_zero
  · exact DifferentiableAt.fun_sum fun l _ =>
      (hA l).mul ((hu l).differentiableAt (by norm_num))

theorem fourHeatOneCovariantDerivative_contDiffAt
    (A : Fin 4 → FourSpace → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 4)
    (hA : ∀ l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    ContDiffAt ℝ 1 (fun y => fourHeatOneCovariantDerivative A u i y k) x := by
  apply ContDiffAt.add
  · exact ((hu k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  · exact ContDiffAt.sum fun l _ => (hA l).mul ((hu l).of_le (by norm_num))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two surviving orders of the signed squared-Gaussian integral. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter Set
open scoped _root_.Topology BigOperators

noncomputable section

theorem fourHeatGaussian_square_amplitude_integrable (f : FourSpace → ℝ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (t : ℝ) (ht : 0 < t) :
    Integrable (fun x => fourHeatGaussian t x ^ 2 * f x) := by
  apply ((fourHeatGaussian_square_integrable t ht).mul_const C).mono'
    (((fourHeatGaussian_continuous t).pow 2).mul hf).aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    change ‖fourHeatGaussian t x ^ 2 * f x‖ ≤ fourHeatGaussian t x ^ 2 * C
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (hC x) (sq_nonneg _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The weighted weak identity for a compact test of the connection
Laplacian. All differential data are the actual coefficient functions. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeat_potential_pairing_integrable
    (u v : FourSpace → Fin 6 → ℝ) (ρ : FourSpace → ℝ)
    (V : FourSpace → HeatMat6) (U : Set FourSpace)
    (hu : ∀ k, Continuous (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContinuousAt (fun y => v y k) x)
    (hρ : ∀ x ∈ U, ContinuousAt ρ x)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x) :
    Integrable (fun x => ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l)) := by
  apply integrable_finsetSum
  intro k _
  have hf (x : FourSpace) (hx : x ∈ tsupport (fun y => u y k)) :
      ContinuousAt (fun y => ρ y * ∑ l, V y k l * v y l) x :=
    (hρ x (hs k hx)).mul (tendsto_finsetSum Finset.univ fun l _ =>
      (hV x (hs k hx) k l).mul (hv x (hs k hx) l))
  have h := fourHeat_local_product_integrable _ _ (hu k) (hc k) hf
  simpa only [mul_comm] using h

theorem fourHeatCovariantOperator_weighted_green
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : FourSpace → HeatMat6)
    (u v : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 2 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x) (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x)
    (hsym : ∀ x ∈ U, ∀ i j, a x i j = a x j i) :
    (∫ x, ∑ k, ρ x * u x k * fourHeatCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      (∑ i : Fin 4, ∫ x, ∑ k : Fin 6,
        fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k) +
      ∫ x, ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l) := by
  let W := fourHeatCovariantFlux A a ρ v
  let B := fun x => ∑ i : Fin 4, ∑ k : Fin 6,
    u x k * fourHeatCovariantDerivative A (W i) i x k
  let P := fun x => ∑ k : Fin 6, u x k * (ρ x * ∑ l : Fin 6, V x k l * v x l)
  have hW (x : FourSpace) (hx : x ∈ U) (i : Fin 4) (k : Fin 6) :
      ContDiffAt ℝ 1 (fun y => W i y k) x :=
    fourHeatCovariantFlux_contDiffAt A a ρ v x i k (fun j l => hA x hx j k l)
      (ha x hx i) (hρ x hx) (hv x hx)
  have hBi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      u x k * fourHeatCovariantDerivative A (W i) i x k) :=
    fourHeatCovariantDerivative_pairing_integrable A u (W i) U i
      (fun k => (hu k).continuous) hc hs (fun x hx k => hW x hx i k)
      (fun x hx k l => (hA x hx i k l).continuousAt)
  have hB : Integrable B := integrable_finsetSum _ (fun i _ => hBi i)
  have hP : Integrable P := fourHeat_potential_pairing_integrable u v ρ V U
    (fun k => (hu k).continuous) hc hs (fun x hx k => (hv x hx k).continuousAt)
    (fun x hx => (hρ x hx).continuousAt) hV
  have heq : (fun x => ∑ k : Fin 6, ρ x * u x k *
      fourHeatCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      fun x => -B x + P x := by
    funext x
    by_cases hx : x ∈ U
    · have hk (k : Fin 6) := fourHeatCovariantOperator_divergence A a ρ (V x) v x k
        (fun i l => (hA x hx i k l).differentiableAt one_ne_zero)
        (fun i j => (ha x hx i j).differentiableAt one_ne_zero)
        ((hρ x hx).differentiableAt one_ne_zero) (hρ0 x hx) (hv x hx) (hsym x hx)
      have hm (k : Fin 6) : ρ x * u x k *
          fourHeatCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) v x k =
          -(∑ i : Fin 4, u x k * fourHeatCovariantDerivative A (W i) i x k) +
            u x k * (ρ x * ∑ l, V x k l * v x l) := by
        calc
          _ = u x k * (ρ x * fourHeatCovariantOperator (a x)
              (fourHeatDensityDrift a ρ x) A (V x) v x k) := by ring
          _ = _ := by rw [hk]; simp only [W, mul_add, mul_neg, Finset.mul_sum]
      simp_rw [hm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_comm (f := fun k i => u x k * fourHeatCovariantDerivative A (W i) i x k)]
    · have hz (k : Fin 6) : u x k = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => u y k) (fun h => hx (hs k h))
      simp only [B, P, hz, mul_zero, zero_mul, Finset.sum_const_zero, neg_zero, zero_add]
  rw [heq, integral_add (f := fun x => -B x) (g := P) hB.neg hP, integral_neg]
  have hgreen := fourHeat_covariant_divergence_green A u W U hu hc hs hW
    (fun x hx i k l => (hA x hx i k l).continuousAt) hskew
  change -(∫ x, B x) + (∫ x, P x) = _
  rw [hgreen, neg_neg]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The flux form of the connection energy has the expected pointwise
symmetry for the actual symmetric principal and potential matrices. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators

noncomputable section

theorem fourHeat_flux_pairing (A : Fin 4 → FourSpace → HeatMat6)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ)
    (u v : FourSpace → Fin 6 → ℝ) (x : FourSpace) :
    (∑ i : Fin 4, ∑ k : Fin 6,
      fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k) =
      ρ x * ∑ k : Fin 6, ∑ i : Fin 4, ∑ j : Fin 4,
        a x i j * fourHeatCovariantDerivative A u i x k * fourHeatCovariantDerivative A v j x k := by
  unfold fourHeatCovariantFlux
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Symmetry of the compact connection flux paired with a local section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators

noncomputable section

theorem fourHeat_flux_pairing_swap
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u v : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (ha : ∀ x ∈ U, ∀ i j, a x i j = a x j i) (x : FourSpace) :
    (∑ i : Fin 4, ∑ k : Fin 6,
      fourHeatCovariantDerivative A v i x k * fourHeatCovariantFlux A a ρ u i x k) =
      ∑ i : Fin 4, ∑ k : Fin 6,
        fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k := by
  by_cases hx : x ∈ U
  · rw [fourHeat_flux_pairing, fourHeat_flux_pairing]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact fourHeat_metric_pairing_symm (a x) (ha x hx)
      (fun i => fourHeatCovariantDerivative A v i x k)
      (fun i => fourHeatCovariantDerivative A u i x k)
  · have hU : (⋃ k, tsupport (fun y => u y k)) ⊆ U := iUnion_subset hs
    have hD (i : Fin 4) (k : Fin 6) : fourHeatCovariantDerivative A u i x k = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantDerivative A u i y k)
        (fun h => hx (hU (fourHeatCovariantDerivative_support A u i k h)))
    have hW (i : Fin 4) (k : Fin 6) : fourHeatCovariantFlux A a ρ u i x k = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantFlux A a ρ u i y k)
        (fun h => hx (hU (fourHeatCovariantFlux_support A a ρ u i k h)))
    simp only [hD, hW, zero_mul, mul_zero, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integrability in the finite-regularity connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeatCovariantDerivative_left_integrable
    (A : Fin 4 → FourSpace → HeatMat6) (u v : FourSpace → Fin 6 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) :
    Integrable (fun x => ∑ k, fourHeatCovariantDerivative A u i x k * v x k) := by
  let F := fun x => ∑ k : Fin 6, u x k * v x k
  have hF : ContDiff ℝ 1 F := fourHeat_pairing_contDiff u v U hu hs hv
  have hcF : HasCompactSupport F := fourHeat_pairing_compact u v hc
  have hDc : Continuous (partialDeriv F i) :=
    ((hF.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have hD : Integrable (partialDeriv F i) :=
    hDc.integrable_of_hasCompactSupport
        (hcF.of_isClosed_subset (isClosed_tsupport _)
          (tsupport_fderiv_apply_subset ℝ (coordinateVector i)))
  have hR := fourHeatCovariantDerivative_pairing_integrable A u v U i
    (fun k => (hu k).continuous) hc hs hv hA
  apply (hD.sub hR).congr
  filter_upwards [] with x
  have hp := fourHeatCovariantDerivative_pairing_global A u v U i hu hs hv hskew x
  change partialDeriv F i x - _ = _
  change partialDeriv F i x = _ at hp
  linarith only [hp]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal-coordinate Hodge operator at every regular point
of a nondegenerate normal chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalFrameData.rough_pullback_at {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det) :
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
  have hgx : ∀ᶠ y in 𝓝 x,
      (D.point y).2ᵀ * metricInChart g c (D.point y).1 * (D.point y).2 = 1 := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact D.orthonormal y hy
  have ha := D.inverseMetric_transport x hx hs hd.ne'
  have hb := D.drift_transport_at x hx hP hs hd
  intro T hT v
  exact heatNormal_rough_pullback g c D.point T x hP hT (D.in_chart x hx) hgx
    (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x) ha hb v

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem HeatNormalFrameData.actual_tensor_rough_at {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (x : FourSpace) (hx : x ∈ ball 0 D.radius)
    (hP : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det) :
    ∀ (u : M → TwoFormFour), TwoFormSmooth o u → ∀ v : Fin 2 → Fin 4,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        tensorCovariantDirection (heatNormalFrameConnection g c D.point)
          (tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i) j x v) +
        (∑ i, heatNormalDrift g o e x i *
          tensorCovariantDirection (heatNormalFrameConnection g c D.point)
            (fun y => frameTensor (D.point y).2 (twoFormCoordinates o u c (D.point y).1)) i x v) =
        -twoFormFramedRoughTrace o u (D.frame x hx) v := by
  have h := D.rough_pullback_at x hx hP hs hd
  intro u hu v
  rw [D.roughTrace_as_actual hu x hx]
  exact h (twoFormCoordinates o u c) (fun z hz => hu.coordinates_contDiffAt c z hz) v

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integration of a divergence whose flux, rather than its test, is compact. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeat_compact_flux_green
    (A : Fin 4 → FourSpace → HeatMat6)
    (W : Fin 4 → FourSpace → Fin 6 → ℝ) (v : FourSpace → Fin 6 → ℝ)
    (U : Set FourSpace)
    (hW : ∀ i k, ContDiff ℝ 1 (fun x => W i x k))
    (hcW : ∀ i k, HasCompactSupport (fun x => W i x k))
    (hsW : ∀ i k, tsupport (fun x => W i x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ i : Fin 4, ∑ k : Fin 6,
      v x k * fourHeatCovariantDerivative A (W i) i x k) =
      -(∑ i : Fin 4, ∫ x, ∑ k : Fin 6,
        fourHeatCovariantDerivative A v i x k * W i x k) := by
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      v x k * fourHeatCovariantDerivative A (W i) i x k) := by
    simpa only [mul_comm] using fourHeatCovariantDerivative_left_integrable A (W i) v U i
      (hW i) (hcW i) (hsW i) hv (fun x hx k l => hA x hx i k l)
      (fun x hx => hskew x hx i)
  rw [integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := fourHeatCovariantDerivative_green A (W i) v U i (hW i) (hcW i) (hsW i)
    hv (fun x hx k l => hA x hx i k l) (fun x hx => hskew x hx i)
  simpa only [mul_comm] using h

theorem fourHeat_potential_pairing_swap
    (u v : FourSpace → Fin 6 → ℝ) (ρ : FourSpace → ℝ)
    (V : FourSpace → HeatMat6) (U : Set FourSpace)
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hV : ∀ x ∈ U, ∀ k l, V x k l = V x l k) (x : FourSpace) :
    (∑ k, v x k * (ρ x * ∑ l, V x k l * u x l)) =
      ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l) := by
  by_cases hx : x ∈ U
  · have hp (p q : Fin 6 → ℝ) : (∑ k, p k * (ρ x * ∑ l, V x k l * q l)) =
        ρ x * ∑ k, p k * ∑ l, V x k l * q l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hp, hp, fourHeat_potential_pairing_symm (V x) (hV x hx)]
  · have hz (k : Fin 6) : u x k = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun y => u y k) (fun h => hx (hs k h))
    simp only [hz, mul_zero, Finset.sum_const_zero, zero_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Formal self-adjointness on a compact C2 amplitude against a local C2
section, with the actual density drift and skew connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set MeasureTheory
open scoped BigOperators ContDiff _root_.Topology

noncomputable section

theorem fourHeatCovariantOperator_compact_adjoint
    (A : Fin 4 → FourSpace → HeatMat6) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : FourSpace → HeatMat6)
    (u v : FourSpace → Fin 6 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 2 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 2 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x) (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hV : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => V y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x)
    (hsym : ∀ x ∈ U, ∀ i j, a x i j = a x j i)
    (hVsym : ∀ x ∈ U, ∀ k l, V x k l = V x l k) :
    (∫ x, ∑ k, ρ x * u x k * fourHeatCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      ∫ x, ∑ k, ρ x * v x k * fourHeatCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) u x k := by
  let W := fourHeatCovariantFlux A a ρ u
  let B := fun x => ∑ i : Fin 4, ∑ k : Fin 6,
    v x k * fourHeatCovariantDerivative A (W i) i x k
  let P := fun x => ∑ k : Fin 6, u x k * (ρ x * ∑ l : Fin 6, V x k l * v x l)
  have hW (i : Fin 4) (k : Fin 6) : ContDiff ℝ 1 (fun x => W i x k) :=
    fourHeatCovariantFlux_contDiff A a ρ u U hu hs hA ha hρ i k
  have hcW (i : Fin 4) (k : Fin 6) : HasCompactSupport (fun x => W i x k) :=
    fourHeatCovariantFlux_compact A a ρ u hc i k
  have hsW (i : Fin 4) (k : Fin 6) : tsupport (fun x => W i x k) ⊆ U :=
    (fourHeatCovariantFlux_support A a ρ u i k).trans (iUnion_subset hs)
  have hBi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      v x k * fourHeatCovariantDerivative A (W i) i x k) := by
    simpa only [mul_comm] using fourHeatCovariantDerivative_left_integrable A (W i) v U i
      (hW i) (hcW i) (hsW i) (fun x hx k => (hv x hx k).of_le (by norm_num))
      (fun x hx k l => (hA x hx i k l).continuousAt) (fun x hx => hskew x hx i)
  have hB : Integrable B := integrable_finsetSum _ (fun i _ => hBi i)
  have hP : Integrable P := fourHeat_potential_pairing_integrable u v ρ V U
    (fun k => (hu k).continuous) hc hs (fun x hx k => (hv x hx k).continuousAt)
    (fun x hx => (hρ x hx).continuousAt) hV
  have heq : (fun x => ∑ k : Fin 6, ρ x * v x k *
      fourHeatCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) u x k) =
      fun x => -B x + P x := by
    funext x
    by_cases hx : x ∈ U
    · have hk (k : Fin 6) := fourHeatCovariantOperator_divergence A a ρ (V x) u x k
        (fun i l => (hA x hx i k l).differentiableAt one_ne_zero)
        (fun i j => (ha x hx i j).differentiableAt one_ne_zero)
        ((hρ x hx).differentiableAt one_ne_zero) (hρ0 x hx)
        (fun l => (hu l).contDiffAt) (hsym x hx)
      have hm (k : Fin 6) : ρ x * v x k *
          fourHeatCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) u x k =
          -(∑ i : Fin 4, v x k * fourHeatCovariantDerivative A (W i) i x k) +
            v x k * (ρ x * ∑ l, V x k l * u x l) := by
        calc
          _ = v x k * (ρ x * fourHeatCovariantOperator (a x)
              (fourHeatDensityDrift a ρ x) A (V x) u x k) := by ring
          _ = _ := by rw [hk]; simp only [W, mul_add, mul_neg, Finset.mul_sum]
      simp_rw [hm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_comm (f := fun k i => v x k * fourHeatCovariantDerivative A (W i) i x k),
        fourHeat_potential_pairing_swap u v ρ V U hs hVsym x]
    · have hz (k : Fin 6) : u x k = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => u y k) (fun h => hx (hs k h))
      have hD (i : Fin 4) (k : Fin 6) : fourHeatCovariantDerivative A u i x k = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantDerivative A u i y k)
          (fun h => hx ((iUnion_subset hs) (fourHeatCovariantDerivative_support A u i k h)))
      have hDD (i j : Fin 4) (k : Fin 6) :
          fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u i) j x k = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun y =>
          fourHeatCovariantDerivative A (fourHeatCovariantDerivative A u i) j y k)
        intro h
        obtain ⟨l, hl⟩ := mem_iUnion.mp (fourHeatCovariantDerivative_support A
          (fourHeatCovariantDerivative A u i) j k h)
        exact hx ((iUnion_subset hs) (fourHeatCovariantDerivative_support A u i l hl))
      have hDW (i : Fin 4) (k : Fin 6) : fourHeatCovariantDerivative A (W i) i x k = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatCovariantDerivative A (W i) i y k)
        intro h
        exact hx ((iUnion_subset (hsW i)) (fourHeatCovariantDerivative_support A (W i) i k h))
      simp only [B, P, fourHeatCovariantOperator, hz, hD, hDD, hDW,
        zero_mul, mul_zero, Finset.sum_const_zero, neg_zero, add_zero]
  have hgreen := fourHeat_compact_flux_green A W v U hW hcW hsW
    (fun x hx k => (hv x hx k).of_le (by norm_num))
    (fun x hx i k l => (hA x hx i k l).continuousAt) hskew
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      fourHeatCovariantDerivative A v i x k * W i x k) := by
    simpa only [mul_comm] using fourHeatCovariantDerivative_pairing_integrable A (W i) v U i
      (fun k => (hW i k).continuous) (hcW i) (hsW i)
      (fun x hx k => (hv x hx k).of_le (by norm_num))
      (fun x hx k l => (hA x hx i k l).continuousAt)
  have hj (i : Fin 4) : Integrable (fun x => ∑ k : Fin 6,
      fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k) :=
    fourHeatCovariantDerivative_left_integrable A u (fourHeatCovariantFlux A a ρ v i) U i
      (fun k => (hu k).of_le (by norm_num)) hc hs
      (fun x hx k => fourHeatCovariantFlux_contDiffAt A a ρ v x i k
        (fun j l => hA x hx j k l) (ha x hx i) (hρ x hx) (hv x hx))
      (fun x hx k l => (hA x hx i k l).continuousAt) (fun x hx => hskew x hx i)
  have hflux : (∑ i : Fin 4, ∫ x, ∑ k : Fin 6,
      fourHeatCovariantDerivative A v i x k * W i x k) =
      ∑ i : Fin 4, ∫ x, ∑ k : Fin 6,
        fourHeatCovariantDerivative A u i x k * fourHeatCovariantFlux A a ρ v i x k := by
    rw [← integral_finsetSum _ (fun i _ => hi i), ← integral_finsetSum _ (fun i _ => hj i)]
    apply integral_congr_ae
    filter_upwards [] with x
    exact fourHeat_flux_pairing_swap A a ρ u v U hs hsym x
  rw [heq, integral_add (f := fun x => -B x) (g := P) hB.neg hP, integral_neg]
  change _ = -(∫ x, B x) + (∫ x, P x)
  rw [hgreen, neg_neg, hflux]
  exact fourHeatCovariantOperator_weighted_green A a ρ V u v U
    (fun k => (hu k).of_le (by norm_num)) hc hs hv hA ha hρ hρ0 hV hskew hsym

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

/-! Normalized gradients of the positive scalar modes form an actual
orthonormal family of exact one-form eigenvectors. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance instCompactSpaceFrameBundle_15_r4eb3af_1 (g : SmoothMetric M) : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
abbrev OneFormExactEigenIndex := {i : ScalarBaseEigenIndex g o d // 0 < scalarBaseHeatRate g o d i}

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint positive-time regularity of the actual cutoff normal kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

theorem fourHeatGaussian_joint_contDiffAt (z : ℝ × FourSpace) (ht : 0 < z.1) :
    ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => fourHeatGaussian w.1 w.2) z := by
  have hP : ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => ((4 * Real.pi * w.1) ^ 2)⁻¹) z :=
    ((contDiffAt_const.mul contDiffAt_fst).pow 2).inv
      (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht.ne'))
  have hN : ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => ‖w.2‖ ^ 2) z :=
    (contDiff_norm_sq ℝ).contDiffAt.comp z contDiffAt_snd
  have hE : ContDiffAt ℝ 2 (fun w : ℝ × FourSpace => -(4 * w.1)⁻¹ * ‖w.2‖ ^ 2) z :=
    (((contDiffAt_const.mul contDiffAt_fst).inv (mul_ne_zero (by norm_num) ht.ne')).neg).mul hN
  exact hP.mul hE.exp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every actual member has the regularity and operator identities needed
for Green's formula throughout its common ball. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.frame_det (N : HeatCommonNormalMember g o c E r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) : (N.frameData.point x).2.det ≠ 0 := by
  intro hz
  have hh := congrArg Matrix.det (N.frameData.orthonormal x (ball_subset_ball N.radius_le hx))
  simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at hh
  norm_num at hh

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact normal-frame signed polynomial and its first jet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def HeatNormalBundleExtension.signedFirst (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  frameExponentialJacobian g o e x * χ x ^ 2 * E.base.U x *
    (twoFormHodgeMatrix * E.amplitude 1 x).trace

def HeatNormalBundleExtension.signedTail (E : HeatNormalBundleExtension D)
    (χ : FourSpace → ℝ) (t : ℝ) (x : FourSpace) : ℝ :=
  frameExponentialJacobian g o e x * χ x ^ 2 *
    (2 * E.base.U x * (twoFormHodgeMatrix * E.amplitude 2 x).trace +
      heatSignedGram (E.amplitude 1 x) (E.amplitude 1 x) +
      t * (2 * E.base.U x * (twoFormHodgeMatrix * E.amplitude 3 x).trace +
        2 * heatSignedGram (E.amplitude 1 x) (E.amplitude 2 x)) +
      t ^ 2 * (2 * heatSignedGram (E.amplitude 1 x) (E.amplitude 3 x) +
        heatSignedGram (E.amplitude 2 x) (E.amplitude 2 x)) +
      t ^ 3 * (2 * heatSignedGram (E.amplitude 2 x) (E.amplitude 3 x)) +
      t ^ 4 * heatSignedGram (E.amplitude 3 x) (E.amplitude 3 x))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


