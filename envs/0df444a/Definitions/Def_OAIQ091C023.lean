-- Prove2me | Definitions.Def_OAIQ091C023
-- name    : OAIQ091C023
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:10:43.306018+00:00
-- url     : https://prove2.me/theorems/a5126947-fb61-469b-b40f-9353f0ecfa15
-- title:
--   Definitions bundle OAIQ091C023 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 161 declarations of OpenAI's Lean: 27 definitions and 134 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.HeatFamilyOneCoefficients.lastCoefficient`, `OAI.PositiveEinsteinFour.Geometry.HeatFamilySmoothCoefficients.scalarLastCoefficient`, `OAI.PositiveEinsteinFour.Geometry.HeatNormalParametrixData.oneOperatorColumn`, `OAI.PositiveEinsteinFour.Geometry.actualFullVariationPosition`, `OAI.PositiveEinsteinFour.Geometry.actualFullVariationVelocity`, `OAI.PositiveEinsteinFour.Geometry.fourHeatConjugatedOperator`, `OAI.PositiveEinsteinFour.Geometry.fourHeatRadialTransport`, `OAI.PositiveEinsteinFour.Geometry.frameGeodesicCoordinateCurve`, `OAI.PositiveEinsteinFour.Geometry.frameGeodesicCoordinateVariation`, `OAI.PositiveEinsteinFour.Geometry.frameKineticCurve`, `OAI.PositiveEinsteinFour.Geometry.frameKineticVariation`, `OAI.PositiveEinsteinFour.Geometry.heatNormalOneHodgeImage`, `OAI.PositiveEinsteinFour.Geometry.smoothHodgeLaplacian`, `OAI.PositiveEinsteinFour.Geometry.smoothL2Curvature`, `OAI.PositiveEinsteinFour.Geometry.smoothL2CurvatureLinear`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormCurvature`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormRoughTrace`, `OAI.PositiveEinsteinFour.Geometry.smoothTwoFormTensorTraceL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormCurvatureBound`, `OAI.PositiveEinsteinFour.Geometry.twoFormCurvatureField`, `OAI.PositiveEinsteinFour.Geometry.twoFormH1ToL2`, `OAI.PositiveEinsteinFour.Geometry.twoFormHodgeCompact`, `OAI.PositiveEinsteinFour.Geometry.twoFormL2Curvature`, `OAI.PositiveEinsteinFour.Geometry.twoFormRoughSolution`, `OAI.PositiveEinsteinFour.Geometry.twoFormShiftedHodge`, `OAI.PositiveEinsteinFour.Geometry.twoFormShiftedHodgeCompact`, `OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockPotential`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory06.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean), [`EinsteinFour_WeylEstimates07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C019` and `OAIQ091C040` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C029`, `OAIQ091C042`, `OAIQ091C045`, `OAIQ091C046`, `OAIQ091C047`, `OAIQ091C049`, `OAIQ091C050`, `OAIQ091C051`, `OAIQ091C052`, `OAIQ091C053`, `OAIQ091C054` and `OAIQ091C056`; the statements `OAI_PositiveEinsteinFour_Boundary_correctedPotential_nonneg` and `OAI_PositiveEinsteinFour_Potential_potential_nonneg`; the proofs of `OAI_PositiveEinsteinFour_Boundary_correctedPotential_nonneg`, `OAI_PositiveEinsteinFour_Energy_remove_energy_defects_from_spectral_bounds` and `OAI_PositiveEinsteinFour_Potential_potential_nonneg`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C019
import Definitions.Def_OAIQ091C040

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

/-! Raising the momentum in the actual kinetic Hamiltonian gives the
ordinary tangent-coordinate geodesic field. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem kineticVelocityCoordinates_curve_derivative (g : SmoothMetric M) (c : M)
    (γ : ℝ → CotangentCoordinates) (dp : CotangentCoordinates) (t : ℝ)
    (hp : (γ t).1 ∈ (chartAt FourSpace c).target)
    (hγ : HasDerivAt γ dp t) :
    HasDerivAt (fun s => kineticVelocityCoordinates g c (γ s))
      (kineticVelocityRate g c (γ t) dp) t := by
  have hH (i j : Fin 4) : HasDerivAt
      (fun s => (metricInChart g c (γ s).1)⁻¹ i j)
      (∑ r, dp.1 r * matrixPartial (fun x => (metricInChart g c x)⁻¹) r
        (γ t).1 i j) t :=
    hasDerivAt_coordinate_comp hγ.fst
      ((metricInChart_inv_contDiffAt g c (γ t).1 hp
        (metricInChart_posDef g c (γ t).1 hp).det_pos.ne' i j).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  have hpj (j : Fin 4) : HasDerivAt (fun s => (γ s).2 j) (dp.2 j) t :=
    (EuclideanSpace.proj j : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hγ.snd
  have hvel : HasDerivAt
      (fun s => (metricInChart g c (γ s).1)⁻¹ *ᵥ WithLp.ofLp (γ s).2)
      (WithLp.ofLp (kineticVelocityRate g c (γ t) dp).2) t := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := HasDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => (hH i j).mul (hpj j))
    simpa only [kineticVelocityRate, Matrix.mulVec, dotProduct, Pi.add_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      Pi.mul_apply] using! h
  exact hγ.fst.prodMk ((PiLp.hasFDerivAt_toLp 2 _).comp_hasDerivAt t hvel)

theorem kineticVelocityCoordinates_fderiv (g : SmoothMetric M) (c : M)
    (p dp : CotangentCoordinates) (hp : p.1 ∈ (chartAt FourSpace c).target) :
    fderiv ℝ (kineticVelocityCoordinates g c) p dp = kineticVelocityRate g c p dp := by
  have hline : HasDerivAt (fun s : ℝ => p + s • dp) dp 0 := by
    simpa only [id_eq, one_smul, zero_add] using!
      (hasDerivAt_const (0 : ℝ) p).add ((hasDerivAt_id (0 : ℝ)).smul_const dp)
  have hrate := kineticVelocityCoordinates_curve_derivative g c
    (fun s : ℝ => p + s • dp) dp 0 (by simpa using hp) hline
  have hderiv := ((kineticVelocityCoordinates_contDiffAt g c p hp).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hderiv' : HasFDerivAt (kineticVelocityCoordinates g c)
      (fderiv ℝ (kineticVelocityCoordinates g c) p) (p + (0 : ℝ) • dp) := by
    simpa only [zero_smul, add_zero] using hderiv
  have hcomp : HasDerivAt (fun s : ℝ => kineticVelocityCoordinates g c (p + s • dp))
      (fderiv ℝ (kineticVelocityCoordinates g c) p dp) 0 :=
    hderiv'.comp_hasDerivAt (f := fun s : ℝ => p + s • dp) 0 hline
  simpa only [zero_smul, add_zero] using hcomp.unique hrate

/-- Exact intertwining of the actual Hamiltonian and geodesic fields. -/
theorem kineticVelocityCoordinates_intertwines (g : SmoothMetric M) (c : M)
    (p : CotangentCoordinates) (hp : p.1 ∈ (chartAt FourSpace c).target) :
    fderiv ℝ (kineticVelocityCoordinates g c) p
      (cotangentHamiltonianField (kineticHamiltonian g c) p) =
      geodesicCoordinateField g c (kineticVelocityCoordinates g c p) := by
  rw [kineticVelocityCoordinates_fderiv g c p _ hp,
    kineticHamiltonianField_coordinates g c p hp]
  apply Prod.ext
  · rfl
  · change WithLp.toLp 2
      ((∑ r, ((metricInChart g c p.1)⁻¹ *ᵥ WithLp.ofLp p.2) r •
          matrixPartial (fun z => (metricInChart g c z)⁻¹) r p.1) *ᵥ
            WithLp.ofLp p.2 +
        (metricInChart g c p.1)⁻¹ *ᵥ
          (fun r => WithLp.ofLp p.2 ⬝ᵥ (connectionMatrix g c r p.1 *ᵥ
            ((metricInChart g c p.1)⁻¹ *ᵥ WithLp.ofLp p.2)))) = _
    rw [kinetic_inverse_metric_rate g c p.1 hp, kinetic_force_transpose]
    exact congrArg (WithLp.toLp 2) (inverse_rate_cancel _ _ _)

theorem kinetic_geodesic_curve (g : SmoothMetric M) (c : M)
    (γ : ℝ → CotangentCoordinates) (t : ℝ)
    (hp : (γ t).1 ∈ (chartAt FourSpace c).target)
    (hγ : HasDerivAt γ
      (cotangentHamiltonianField (kineticHamiltonian g c) (γ t)) t) :
    HasDerivAt (fun s => kineticVelocityCoordinates g c (γ s))
      (geodesicCoordinateField g c (kineticVelocityCoordinates g c (γ t))) t := by
  have h := ((kineticVelocityCoordinates_contDiffAt g c (γ t) hp).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt t hγ
  rw [kineticVelocityCoordinates_intertwines g c (γ t) hp] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The metric's actual four-tensor in moving orthonormal frames, with
its chart realization and uniform bound on a closed manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem twoFormMetricCurvatureTensor_continuous (g : SmoothMetric M) :
    Continuous (twoFormMetricCurvatureTensor g) := by
  apply continuous_framedTensor g (curvatureCoordinates g)
  · intro c z hz a
    exact (curvatureCoordinates_contDiffAt g c z hz
      (metricInChart_posDef g c z hz).det_pos.ne' a).continuousAt
  · exact curvatureCoordinates_transition g

theorem twoFormMetricCurvatureTensor_change (g : SmoothMetric M) {x : M}
    (e f : OrthonormalFrame g x) :
    twoFormMetricCurvatureTensor g ⟨x,f⟩ =
      frameTensor (e.changeMatrix f) (twoFormMetricCurvatureTensor g ⟨x,e⟩) := by
  unfold twoFormMetricCurvatureTensor
  rw [← frameTensor_mul, e.mul_changeMatrix f]

theorem twoFormMetricCurvatureTensor_chart (g : SmoothMetric M) (c : M) (S : Mat4)
    (hS : Sᵀ * S = 1) (z : ChartTarget c) :
    twoFormMetricCurvatureTensor g (chartGramSection g c S hS z) =
      frameTensor (chartGramMatrix g c S z) (curvatureCoordinates g c z) := by
  have hc := curvatureCoordinates_transition g c ((chartAt FourSpace c).symm z) z z.property
    (mem_chart_source FourSpace ((chartAt FourSpace c).symm z))
  rw [chartTransitionMatrix_to_center c z z.property] at hc
  rw [hc, ← frameTensor_mul]
  rfl

theorem twoFormMetricCurvatureTensor_bound [T3Space M] [CompactSpace M]
    (g : SmoothMetric M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ e : FrameBundle g, ‖twoFormMetricCurvatureTensor g e‖ ≤ C := by
  let _ := actual_compactFrameBundle g
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image
    (twoFormMetricCurvatureTensor_continuous g).norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun e => ?_⟩
  exact (hC ⟨e, mem_univ e, rfl⟩).trans (le_max_left _ _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The initial normal data of a vertical momentum variation.
The raising map and inverse orthonormal frame determine these data exactly. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- A momentum change obtained by lowering `w` raises back to `w`, with
zero change of the base point. -/
theorem kineticVelocityCoordinates_vertical_fderiv (g : SmoothMetric M) (c : M)
    (p : CotangentCoordinates) (w : Fin 4 → ℝ)
    (hp : p.1 ∈ (chartAt FourSpace c).target) :
    fderiv ℝ (kineticVelocityCoordinates g c) p
      (0, WithLp.toLp 2 (metricInChart g c p.1 *ᵥ w)) =
        (0, WithLp.toLp 2 w) := by
  rw [kineticVelocityCoordinates_fderiv g c p _ hp]
  change (0, WithLp.toLp 2
    ((∑ r, (0 : FourSpace) r •
        matrixPartial (fun x => (metricInChart g c x)⁻¹) r p.1) *ᵥ
          WithLp.ofLp p.2 +
      (metricInChart g c p.1)⁻¹ *ᵥ (metricInChart g c p.1 *ᵥ w))) = _
  have hz : (∑ r, (0 : FourSpace) r •
      matrixPartial (fun x => (metricInChart g c x)⁻¹) r p.1) = 0 := by
    simp only [PiLp.zero_apply, zero_smul, Finset.sum_const_zero]
  rw [hz, Matrix.zero_mulVec, zero_add, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (metricInChart_posDef g c p.1 hp).det_pos.ne'),
    Matrix.one_mulVec]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full inverse-frame variational equation. The head is the radial
component, whose acceleration vanishes; its zero-position solution is linear. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The actual frame variation has zero radial acceleration and the true
normal Jacobi acceleration. -/
theorem actual_geodesic_frame_variation (g : SmoothMetric M) (c : M)
    (e : ℝ → FrameBundle g) (γ Z : ℝ → FourSpace × FourSpace) (t : ℝ)
    (hc : (e t).base ∈ (chartAt FourSpace c).source)
    (hposition : (γ t).1 = chartAt FourSpace c (e t).base)
    (hvelocity : WithLp.ofLp (γ t).2 = fun i => frameChartMatrix g c (e t) i 0)
    (hγ : HasDerivAt γ (geodesicCoordinateField g c (γ t)) t)
    (hZ : HasDerivAt Z (fderiv ℝ (geodesicCoordinateField g c) (γ t) (Z t)) t)
    (hE : ∀ i j, HasDerivAt (fun s => frameChartMatrix g c (e s) i j)
      (-(jacobiConnection (fun k => connectionMatrix g c k (γ t).1)
        (WithLp.ofLp (γ t).2) * frameChartMatrix g c (e t)) i j) t) :
    HasDerivAt (geodesicFramePosition g c e Z)
      (geodesicFrameVelocity g c e γ Z t) t ∧
      HasDerivAt (geodesicFrameVelocity g c e γ Z)
        (-(Fin.cons 0 ((1 + frameCurvatureField g (e t)) *ᵥ
          geodesicNormalPosition g c e Z t))) t := by
  let E : ℝ → Mat4 := fun s => frameChartMatrix g c (e s)
  let Y : ℝ → JacobiCoordinateVector := fun s => WithLp.ofLp (Z s).1
  let F := geodesicVariationCovariantDerivative g c γ Z
  let U := jacobiConnection (fun k => connectionMatrix g c k (γ t).1)
    (WithLp.ofLp (γ t).2)
  have hz : (γ t).1 ∈ (chartAt FourSpace c).target := by
    rw [hposition]
    exact (chartAt FourSpace c).map_source hc
  have hdet : (E t).det ≠ 0 :=
    (Matrix.isUnit_det_of_left_inverse (frameChartMatrix_normalizes g c (e t) hc)).ne_zero
  have hvar := geodesic_variation_derivatives g c γ Z t hz hZ
  have hY : HasDerivAt Y (WithLp.ofLp (Z t).2) t := by
    apply hasDerivAt_pi.mpr
    intro i
    exact (EuclideanSpace.proj i : FourSpace →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hvar.1
  have hF : HasDerivAt F (deriv F t) t :=
    (geodesic_variation_covariant_differentiableAt g c γ Z t hz
      hγ.differentiableAt hZ.differentiableAt).hasDerivAt
  have hp := inverseFrameComponents_covariant_pair E Y F U
    (WithLp.ofLp (Z t).2) (deriv F t) t hE hY hF rfl hdet
  have hJac := geodesic_variation_jacobi g c γ Z t hz hγ hZ
  change deriv F t + U *ᵥ F t + jacobiCurvatureCombination
    (fun i j => coordinateCurvatureMatrix g c i j (γ t).1)
    (Y t) (WithLp.ofLp (γ t).2) *ᵥ WithLp.ofLp (γ t).2 = 0 at hJac
  have hforce : deriv F t + U *ᵥ F t =
      -(jacobiCurvatureCombination
        (fun i j => coordinateCurvatureMatrix g c i j (γ t).1)
        (Y t) (WithLp.ofLp (γ t).2) *ᵥ WithLp.ofLp (γ t).2) :=
    eq_neg_of_add_eq_zero_left hJac
  have hYvalue : E t *ᵥ geodesicFramePosition g c e Z t = Y t :=
    inverseFrameComponents_mul E Y t hdet
  have hcurv : (E t)⁻¹ *ᵥ (jacobiCurvatureCombination
      (fun i j => coordinateCurvatureMatrix g c i j (γ t).1)
      (Y t) (WithLp.ofLp (γ t).2) *ᵥ WithLp.ofLp (γ t).2) =
      Fin.cons 0 ((1 + frameCurvatureField g (e t)) *ᵥ
        geodesicNormalPosition g c e Z t) := by
    rw [← hYvalue]
    simp only [hposition, hvelocity]
    exact frameChart_normal_jacobi_curvature g c (e t) hc
      (geodesicFramePosition g c e Z t)
  refine ⟨hp.1, ?_⟩
  have h := hp.2
  rw [hforce, Matrix.mulVec_neg, hcurv] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! A C² coordinate conjugacy transports the first variational equation.
Only the coordinate map is differentiated twice; a C² flow is not assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

/-- The first variation of the actual kinetic flow becomes the first
variation of the actual geodesic field after raising momentum. -/
theorem kinetic_geodesic_variation (g : SmoothMetric M) (c : M)
    (γ Z : ℝ → CotangentCoordinates) (t : ℝ)
    (hp : (γ t).1 ∈ (chartAt FourSpace c).target)
    (hγ : HasDerivAt γ
      (cotangentHamiltonianField (kineticHamiltonian g c) (γ t)) t)
    (hZ : HasDerivAt Z
      (fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g c)) (γ t) (Z t)) t) :
    HasDerivAt (fun s => fderiv ℝ (kineticVelocityCoordinates g c) (γ s) (Z s))
      (fderiv ℝ (geodesicCoordinateField g c)
        (kineticVelocityCoordinates g c (γ t))
        (fderiv ℝ (kineticVelocityCoordinates g c) (γ t) (Z t))) t := by
  apply variational_equation_of_intertwining
    (kineticVelocityCoordinates g c)
    (cotangentHamiltonianField (kineticHamiltonian g c))
    (geodesicCoordinateField g c) γ Z t
  · exact (kineticVelocityCoordinates_contDiffAt g c (γ t) hp).of_le (by norm_num)
  · exact (kineticHamiltonianField_contDiffAt g c (γ t) hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · exact (geodesicCoordinateField_contDiffAt g c
      (kineticVelocityCoordinates g c (γ t)) hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  · have hnear : ∀ᶠ p : CotangentCoordinates in 𝓝 (γ t),
        p.1 ∈ (chartAt FourSpace c).target :=
      continuous_fst.continuousAt.eventually ((chartAt FourSpace c).open_target.mem_nhds hp)
    filter_upwards [hnear] with p hp
    exact kineticVelocityCoordinates_intertwines g c p hp
  · exact hγ
  · exact hZ

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

def twoFormCurvatureField (o : FrameOrientation g) (u : M → TwoFormFour) : M → TwoFormFour :=
  fun x => twoFormCurvatureAction (twoFormMetricCurvatureTensor g ⟨x,o.frame x⟩) (u x)

theorem twoFormCurvatureField_frame (u : M → TwoFormFour) (e : FrameBundle g) :
    twoFormFrameValue o (twoFormCurvatureField o u) e =
      twoFormCurvatureAction (twoFormMetricCurvatureTensor g e) (twoFormFrameValue o u e) := by
  let P := (o.frame e.base).changeMatrix e.frame
  have hP : P * Pᵀ = 1 := mul_eq_one_comm.mp ((o.frame e.base).changeMatrix_orthogonal e.frame)
  have he : twoFormMetricCurvatureTensor g e =
      frameTensor P (twoFormMetricCurvatureTensor g ⟨e.base,o.frame e.base⟩) :=
    twoFormMetricCurvatureTensor_change g (o.frame e.base) e.frame
  have hs : ∀ i j k l,
      frameTensor P (twoFormMetricCurvatureTensor g ⟨e.base,o.frame e.base⟩) ![j,i,k,l] =
      -frameTensor P (twoFormMetricCurvatureTensor g ⟨e.base,o.frame e.base⟩) ![i,j,k,l] := by
    intro i j k l
    rw [← he]
    exact twoFormMetricCurvatureTensor_skew g e i j k l
  change twoFormFrameAction P (twoFormCurvatureAction
    (twoFormMetricCurvatureTensor g ⟨e.base,o.frame e.base⟩) (u e.base)) = _
  rw [he]
  exact (twoFormCurvatureAction_frame P hP _
    (twoFormMetricCurvatureTensor_skew g ⟨e.base,o.frame e.base⟩) hs (u e.base)).symm

theorem TwoFormSmooth.curvature {u : M → TwoFormFour} (hu : TwoFormSmooth o u) :
    TwoFormSmooth o (twoFormCurvatureField o u) := by
  intro c S hS U hU hUt hp
  have hR : ContDiffOn ℝ ∞ (fun w => frameTensor (chartGramMatrix g c S w)
      (curvatureCoordinates g c w)) U := by
    intro z hz
    exact (chartMetricCurvature_contDiffAt c S z (hUt hz)).contDiffWithinAt
  have hA := (twoFormCurvatureOperator.contDiff.comp_contDiffOn hR).clm_apply
    (hu c S hS U hU hUt hp)
  apply hA.congr
  intro z hz
  change twoFormChartValue o (twoFormCurvatureField o u) c S hS z =
    twoFormCurvatureAction _ (twoFormChartValue o u c S hS z)
  simp only [twoFormChartValue, dite_eq_left (hUt hz)]
  rw [twoFormCurvatureField_frame, twoFormMetricCurvatureTensor_chart]

def smoothTwoFormCurvature (u : smoothTwoForms o) : smoothTwoForms o :=
  ⟨twoFormCurvatureField o u.val, u.property.curvature⟩

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

def twoFormH1ToL2 : TwoFormH1 o →L[ℝ] TwoFormL2 o :=
  ((smoothTwoFormToL2 (o := o)).toContinuousLinearMap.comp smoothH1ToL2).fromCompletion

end
end PositiveEinsteinFour.Geometry
end


section

/-! Full radial and normal initial components of a vertical momentum
variation, without requiring that the initial velocity be normal. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem geodesicFrame_initial_of_vertical (g : SmoothMetric M) (c : M)
    (e : ℝ → FrameBundle g) (γ Z : ℝ → FourSpace × FourSpace)
    (w : Fin 4 → ℝ) (t : ℝ)
    (he : (e t).base ∈ (chartAt FourSpace c).source)
    (hZ : Z t = (0, WithLp.toLp 2 (frameChartMatrix g c (e t) *ᵥ w))) :
    geodesicFramePosition g c e Z t = 0 ∧
      geodesicFrameVelocity g c e γ Z t = w := by
  have hdet : IsUnit (frameChartMatrix g c (e t)).det :=
    Matrix.isUnit_det_of_left_inverse (frameChartMatrix_normalizes g c (e t) he)
  constructor
  · change (frameChartMatrix g c (e t))⁻¹ *ᵥ WithLp.ofLp (Z t).1 = 0
    rw [hZ]
    exact Matrix.mulVec_zero _
  · change (frameChartMatrix g c (e t))⁻¹ *ᵥ
      (WithLp.ofLp (Z t).2 +
        jacobiConnection (fun i => connectionMatrix g c i (γ t).1)
          (WithLp.ofLp (γ t).2) *ᵥ WithLp.ofLp (Z t).1) = _
    rw [hZ]
    simp only [WithLp.ofLp_zero, Matrix.mulVec_zero, add_zero]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem kinetic_frame_initial_data (g : SmoothMetric M) (c : M)
    (e : ℝ → FrameBundle g) (γ Z : ℝ → FourSpace × FourSpace)
    (p : CotangentCoordinates) (w : Fin 4 → ℝ) (t : ℝ)
    (he : (e t).base ∈ (chartAt FourSpace c).source)
    (hp : p.1 ∈ (chartAt FourSpace c).target)
    (hZ : Z t = fderiv ℝ (kineticVelocityCoordinates g c) p
      (0, WithLp.toLp 2 (metricInChart g c p.1 *ᵥ
        (frameChartMatrix g c (e t) *ᵥ w)))) :
    geodesicFramePosition g c e Z t = 0 ∧
      geodesicFrameVelocity g c e γ Z t = w := by
  apply geodesicFrame_initial_of_vertical g c e γ Z w t he
  rw [hZ, kineticVelocityCoordinates_vertical_fderiv g c p _ hp]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual derivative of the complete radial flow, expressed in a
parallel orthonormal frame along its unit-speed geodesic. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

def frameKineticCurve (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (e : FrameBundle g) (t : ℝ) : CotangentCoordinates :=
  unitRadialCotangentState g c (unitTangentRadialFlow g o t (frameUnitRadialState e))

def frameKineticVariation (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (e : FrameBundle g) (a : CotangentCoordinates) (t : ℝ) : CotangentCoordinates :=
  fderiv ℝ (radialCoordinateFlow g o e.base c t)
    (unitRadialCotangentState g e.base (frameUnitRadialState e)) a

def frameGeodesicCoordinateCurve (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (e : FrameBundle g) (t : ℝ) : FourSpace × FourSpace :=
  kineticVelocityCoordinates g c (frameKineticCurve g o c e t)

def frameGeodesicCoordinateVariation (g : SmoothMetric M) (o : FrameOrientation g) (c : M)
    (e : FrameBundle g) (a : CotangentCoordinates) (t : ℝ) : FourSpace × FourSpace :=
  fderiv ℝ (kineticVelocityCoordinates g c) (frameKineticCurve g o c e t)
    (frameKineticVariation g o c e a t)

theorem frameUnitRadialState_flow (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    (unitTangentRadialFlow g o t (frameUnitRadialState e)).2 =
      unitTangentOfFrame (parallelFrameFlowMap g 0 t e) := by
  change unitTangentFlowMap g o (1 * t) (unitTangentOfFrame e) = _
  rw [one_mul, unitTangentFlowMap_of_frame g o t e he]

theorem frameKineticCurve_eq (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    frameKineticCurve g o c e t =
      unitCotangentState g c 1 (unitTangentOfFrame (parallelFrameFlowMap g 0 t e)) := by
  change unitCotangentState g c 1
    (unitTangentRadialFlow g o t (frameUnitRadialState e)).2 = _
  rw [frameUnitRadialState_flow g o e he t]

theorem frameGeodesicCoordinateCurve_position (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) :
    (frameGeodesicCoordinateCurve g o c e t).1 =
      chartAt FourSpace c (parallelFrameFlowMap g 0 t e).base := by
  change (frameKineticCurve g o c e t).1 = _
  rw [frameKineticCurve_eq g o c e he t]
  rfl

theorem frameGeodesicCoordinateCurve_velocity (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    WithLp.ofLp (frameGeodesicCoordinateCurve g o c e t).2 =
      fun i => frameChartMatrix g c (parallelFrameFlowMap g 0 t e) i 0 := by
  change WithLp.ofLp (raisedChartVelocity g c (frameKineticCurve g o c e t)) = _
  rw [frameKineticCurve_eq g o c e he t,
    raisedChartVelocity_unitCotangentState g c 1 _ hc, one_smul]
  rfl

theorem frameKineticCurve_hasDerivAt (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (frameKineticCurve g o c e)
      (cotangentHamiltonianField (kineticHamiltonian g c) (frameKineticCurve g o c e t)) t := by
  apply hasDerivAt_unitTangentRadial_cotangent g o c (frameUnitRadialState e) t
  simpa only [frameUnitRadialState_flow g o e he t, unitTangentOfFrame] using hc

theorem frameKineticVariation_hasDerivAt (g : SmoothMetric M) (o : FrameOrientation g)
    (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (frameKineticVariation g o c e a)
      (fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g c))
        (frameKineticCurve g o c e t) (frameKineticVariation g o c e a t)) t := by
  have hd := radialCoordinateFlow_fderiv_hasDerivAt g o e.base c (frameUnitRadialState e) t
    (mem_chart_source FourSpace e.base) (by
      simpa only [frameUnitRadialState_flow g o e he t, unitTangentOfFrame] using hc)
  simpa only [ContinuousLinearMap.comp_apply, map_zero, add_zero] using! hd.clm_apply (hasDerivAt_const t a)

theorem frameGeodesicCoordinateCurve_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (frameGeodesicCoordinateCurve g o c e)
      (geodesicCoordinateField g c (frameGeodesicCoordinateCurve g o c e t)) t := by
  apply kinetic_geodesic_curve g c (frameKineticCurve g o c e) t
  · rw [frameKineticCurve_eq g o c e he t]
    exact (chartAt FourSpace c).map_source hc
  · exact frameKineticCurve_hasDerivAt g o c e he t hc

theorem frameGeodesicCoordinateVariation_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (frameGeodesicCoordinateVariation g o c e a)
      (fderiv ℝ (geodesicCoordinateField g c) (frameGeodesicCoordinateCurve g o c e t)
        (frameGeodesicCoordinateVariation g o c e a t)) t := by
  apply kinetic_geodesic_variation g c (frameKineticCurve g o c e)
    (frameKineticVariation g o c e a) t
  · rw [frameKineticCurve_eq g o c e he t]
    exact (chartAt FourSpace c).map_source hc
  · exact frameKineticCurve_hasDerivAt g o c e he t hc
  · exact frameKineticVariation_hasDerivAt g o c e he a t hc


theorem frameGeodesicCoordinateVariation_fst (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    (frameGeodesicCoordinateVariation g o c e a t).1 =
      (frameKineticVariation g o c e a t).1 := by
  have hp : (frameKineticCurve g o c e t).1 ∈ (chartAt FourSpace c).target := by
    rw [frameKineticCurve_eq g o c e he t]
    exact (chartAt FourSpace c).map_source hc
  change (fderiv ℝ (kineticVelocityCoordinates g c) _ _).1 = _
  rw [kineticVelocityCoordinates_fderiv g c _ _ hp]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! The two-form rough Green identity from the actual invariant parallel
flows. No integration-by-parts input is added to the geometry. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.twoFormGreen_compactFrame
theorem smoothTwoForm_direction_green (hRic : RicciThree g) (u v : smoothTwoForms o)
    (i : Fin 4) (a : Fin 2 → Fin 4) :
    (∫ e, twoFormFramedCovariantDerivative o u.val e (Fin.cons i a) *
      twoFormFramedCovariantDerivative o v.val e (Fin.cons i a) ∂canonicalFrameMeasure g o) =
      -(∫ e, twoFormFramedValue o u.val e a *
        twoFormFramedSecondDerivative o v.val e (Fin.cons i (Fin.cons i a))
        ∂canonicalFrameMeasure g o) := by
  let d := canonicalParallelMetricData g o hRic
  let F : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedValue o u.val e a,
    (continuous_apply a).comp u.property.continuous_framedValue⟩
  let DF : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedCovariantDerivative o u.val e (Fin.cons i a),
    (continuous_apply _).comp u.property.continuous_framedCovariantDerivative⟩
  let H : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedCovariantDerivative o v.val e (Fin.cons i a),
    (continuous_apply _).comp v.property.continuous_framedCovariantDerivative⟩
  let DH : C(FrameBundle g, ℝ) := ⟨fun e => twoFormFramedSecondDerivative o v.val e (Fin.cons i (Fin.cons i a)),
    (continuous_apply _).comp v.property.continuous_framedSecondDerivative⟩
  apply scalar_flow_green (d := d.toMetricGreenData) i F DF H DH
  · intro t e
    exact u.property.framedValue_parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) a
  · intro t e
    exact v.property.framedCovariant_parallel_derivative (fun s => (d.flow i).map s e) t i
      (d.curve_continuous i e).continuousAt (d.parallelCurve i t e) (Fin.cons i a)

theorem smoothTwoForm_rough_green (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothTwoFormCovariantEnergy u v = -(1 / 2 : ℝ) *
      ∫ e, frameTensorPairing (twoFormFramedValue o u.val e)
        (twoFormFramedRoughTrace o v.val e) ∂canonicalFrameMeasure g o := by
  let μ := canonicalFrameMeasure g o
  let A : Fin 4 → (Fin 2 → Fin 4) → FrameBundle g → ℝ := fun i a e =>
    twoFormFramedCovariantDerivative o u.val e (Fin.cons i a) *
      twoFormFramedCovariantDerivative o v.val e (Fin.cons i a)
  let B : Fin 4 → (Fin 2 → Fin 4) → FrameBundle g → ℝ := fun i a e =>
    twoFormFramedValue o u.val e a *
      twoFormFramedSecondDerivative o v.val e (Fin.cons i (Fin.cons i a))
  have hA (i : Fin 4) (a : Fin 2 → Fin 4) : Integrable (A i a) μ :=
    (((continuous_apply _).comp u.property.continuous_framedCovariantDerivative).mul
      ((continuous_apply _).comp v.property.continuous_framedCovariantDerivative)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hB (i : Fin 4) (a : Fin 2 → Fin 4) : Integrable (B i a) μ :=
    (((continuous_apply _).comp u.property.continuous_framedValue).mul
      ((continuous_apply _).comp v.property.continuous_framedSecondDerivative)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : (∫ e, ∑ i, ∑ a, A i a e ∂μ) = -(∫ e, ∑ a, ∑ i, B i a e ∂μ) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun a _ => hA i a)),
      integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun i _ => hB i a))]
    simp_rw [integral_finsetSum _ (fun a _ => hA _ a),
      integral_finsetSum _ (fun i _ => hB i _)]
    have hi (i : Fin 4) (a : Fin 2 → Fin 4) : (∫ e, A i a e ∂μ) = -(∫ e, B i a e ∂μ) :=
      smoothTwoForm_direction_green hRic u v i a
    simp_rw [hi, Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  have he : (fun e : FrameBundle g => twoFormCovariantPairing o u.val v.val e.base) =
      fun e => (1 / 2 : ℝ) * ∑ i, ∑ a, A i a e := by
    funext e
    rw [twoFormCovariantPairing_eq_frame]
    unfold frameTensorPairing
    rw [sum_tensor_indices_cons]
  unfold smoothTwoFormCovariantEnergy
  rw [← canonicalFrameMeasure_integral_base g o _ (smoothTwoFormCovariantPairing_integrable u v),
    he, integral_const_mul, hg]
  have hr : (fun e => ∑ a, ∑ i, B i a e) = fun e =>
      frameTensorPairing (twoFormFramedValue o u.val e) (twoFormFramedRoughTrace o v.val e) := by
    funext e
    simp only [B, frameTensorPairing, twoFormFramedRoughTrace, Finset.mul_sum]
  rw [hr]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual rough Green pairing is bounded by the L2 value norm.
This is the estimate needed to close the covariant derivative graph. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.twoFormBound_compactFrame
def smoothTwoFormTensorTraceL2 (u : smoothTwoForms o) : Lp TwoTensorEuclidean 2 (canonicalFrameMeasure g o) :=
  ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanTrace u)

theorem smoothTwoFormTensorValueTrace_inner (u v : smoothTwoForms o) :
    inner ℝ (smoothTwoFormTensorValueL2 u) (smoothTwoFormTensorTraceL2 v) =
      ∫ e, frameTensorPairing (twoFormFramedValue o u.val e)
        (twoFormFramedRoughTrace o v.val e) ∂canonicalFrameMeasure g o := by
  change inner ℝ (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanValue u))
    (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ (smoothTwoFormEuclideanTrace v)) = _
  rw [continuousTwoTensor_inner_toLp]
  apply integral_congr_ae
  filter_upwards [] with e
  change (∑ a, inner ℝ (twoFormFramedValue o u.val e a) (twoFormFramedRoughTrace o v.val e a)) = _
  simp only [RCLike.inner_apply, conj_trivial, frameTensorPairing, mul_comm]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual covariant derivative retains the alternating two-form slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.framedCovariant_skew (hRic : RicciThree g) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (e : FrameBundle g) (i j k : Fin 4) :
    twoFormFramedCovariantDerivative o u e ![i,k,j] =
      -twoFormFramedCovariantDerivative o u e ![i,j,k] := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow i).map t e
  have hzero : γ 0 = e :=
    actualParallelMetricData_zero g (canonicalFrameMeasure g o)
      (parallelFrameFlowMap_measurePreserving g o) hRic i e
  have hk := hu.framedValue_parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![k,j]
  have hj := (hu.framedValue_parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,k]).neg
  have heq : (fun t => -(twoFormFramedValue o u (γ t) ![j,k])) =
      fun t => twoFormFramedValue o u (γ t) ![k,j] := by
    funext t
    exact (twoFormFramedValue_skew u (γ t) j k).symm
  change HasDerivAt (fun t => -(twoFormFramedValue o u (γ t) ![j,k]))
    (-twoFormFramedCovariantDerivative o u (γ 0) (Fin.cons i ![j,k])) 0 at hj
  rw [heq] at hj
  have h := hk.unique hj
  rw [hzero] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal differential of the actual exponential is the global
Jacobi matrix. The initial velocity is varied in its actual frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

omit [T2Space M] [CompactSpace M] in
theorem frameUnitRadialState_cotangent (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) :
    unitRadialCotangentState g c (frameUnitRadialState e) =
      (chartAt FourSpace c e.base, frameMomentumMap g c e (coordinateVector 0)) := by
  rw [frameMomentumMap_apply g c e he]
  change (chartAt FourSpace c e.base, 1 • WithLp.toLp 2
    (metricInChart g c (chartAt FourSpace c e.base) *ᵥ
      (fun i => frameChartMatrix g c e i 0))) = _
  rw [one_smul]
  congr 2
  simp [coordinateVector]
  rfl

theorem frameExponential_rescaled_hasFDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (d : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    HasFDerivAt (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e (t • v)))
      ((ContinuousLinearMap.fst ℝ FourSpace FourSpace).comp
        ((fderiv ℝ (radialCoordinateFlow g o e.base d t)
          (unitRadialCotangentState g e.base (frameUnitRadialState e))).comp
          ((0 : FourSpace →L[ℝ] FourSpace).prod (frameMomentumMap g e.base e))))
      (coordinateVector 0) := by
  have hc : e.base ∈ (chartAt FourSpace e.base).source := mem_chart_source FourSpace e.base
  have hD := ((radialFlowContDiffAt_all_time g o t (frameUnitRadialState e) e.base d hc
    (by simpa only [frameUnitRadialState_flow g o e he t, unitTangentOfFrame] using hd)).differentiableAt
      (by first | simp | exact_mod_cast le_top)).hasFDerivAt
  rw [frameUnitRadialState_cotangent g e.base e hc] at hD
  have hinit : HasFDerivAt
      (fun v : FourSpace => (chartAt FourSpace e.base e.base, frameMomentumMap g e.base e v))
      ((0 : FourSpace →L[ℝ] FourSpace).prod (frameMomentumMap g e.base e))
      (coordinateVector 0) :=
    (hasFDerivAt_const _ _).prodMk (frameMomentumMap g e.base e).hasFDerivAt
  have hcomp := (hD.comp (coordinateVector 0) hinit).fst
  have hv : coordinateVector (0 : Fin 4) ≠ 0 := by
    intro h
    have hh := congrArg (fun v : FourSpace => v 0) h
    norm_num [coordinateVector] at hh
  have heq : (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e (t • v)))
      =ᶠ[𝓝 (coordinateVector 0)]
      (fun v => (radialCoordinateFlow g o e.base d t
        (chartAt FourSpace e.base e.base, frameMomentumMap g e.base e v)).1) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hv] with v hv
    exact (radialCoordinateFlow_frame_endpoint_time g o e.base d e hc t ht v hv).symm
  have h := hcomp.congr_of_eventuallyEq heq
  rw [← frameUnitRadialState_cotangent g e.base e hc] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The full actual variation in a parallel frame. The radial component
has zero acceleration and the normal component is the Jacobi system. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem frameGeodesic_full_variation (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    HasDerivAt (geodesicFramePosition g c (parallelFrameFlowMap g 0 · e)
      (frameGeodesicCoordinateVariation g o c e a))
      (geodesicFrameVelocity g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) t) t ∧
    HasDerivAt (geodesicFrameVelocity g c (parallelFrameFlowMap g 0 · e)
      (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a))
      (-(Fin.cons 0 ((1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) *ᵥ
        geodesicNormalPosition g c (parallelFrameFlowMap g 0 · e)
          (frameGeodesicCoordinateVariation g o c e a) t))) t := by
  apply actual_geodesic_frame_variation g c (parallelFrameFlowMap g 0 · e)
    (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) t hc
  · exact frameGeodesicCoordinateCurve_position g o c e he t
  · exact frameGeodesicCoordinateCurve_velocity g o c e he t hc
  · exact frameGeodesicCoordinateCurve_hasDerivAt g o c e he t hc
  · exact frameGeodesicCoordinateVariation_hasDerivAt g o c e he a t hc
  · have h := parallelFrameCurveAt_fixedChart g c (parallelFrameFlowMap g 0 · e) t 0
      (parallelFrameFlowMap_curve_continuous g 0 e).continuousAt hc
      (parallelFrameFlowMap_primitive g 0 e t)
    have hE := (ContinuousLinearMap.snd ℝ FourSpace Mat4).hasFDerivAt.comp_hasDerivAt t h
    rw [frameGeodesicCoordinateCurve_position g o c e he t,
      frameGeodesicCoordinateCurve_velocity g o c e he t hc]
    exact fun i j => hasDerivAt_pi.mp (hasDerivAt_pi.mp hE i) j

def actualFullVariationPosition (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (a : CotangentCoordinates) (t : ℝ) : Fin 4 → ℝ :=
  radialVariationInFrame g o e.base (parallelFrameFlowMap g 0 t e).base
    (frameUnitRadialState e) t (parallelFrameFlowMap g 0 t e) a

def actualFullVariationVelocity (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (a : CotangentCoordinates) : ℝ → Fin 4 → ℝ :=
  deriv (actualFullVariationPosition g o e a)

theorem actualFullVariationPosition_eq_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    actualFullVariationPosition g o e a t =
      geodesicFramePosition g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateVariation g o c e a) t := by
  have hb : (parallelFrameFlowMap g 0 t e).base =
      (unitTangentRadialFlow g o t (frameUnitRadialState e)).2.base :=
    (congrArg UnitTangentBundle.base (frameUnitRadialState_flow g o e he t)).symm
  have h := radialVariationInFrame_chart_independent g o e.base
    (parallelFrameFlowMap g 0 t e).base c (frameUnitRadialState e) t
    (parallelFrameFlowMap g 0 t e) a (mem_chart_source FourSpace e.base) hb
    (mem_chart_source FourSpace _) hc
  change actualFullVariationPosition g o e a t =
    (frameChartMatrix g c (parallelFrameFlowMap g 0 t e))⁻¹ *ᵥ WithLp.ofLp
      (frameGeodesicCoordinateVariation g o c e a t).1
  rw [frameGeodesicCoordinateVariation_fst g o c e he a t hc]
  exact h

theorem actualFullVariationPosition_eventually_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    actualFullVariationPosition g o e a =ᶠ[𝓝 t]
      geodesicFramePosition g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateVariation g o c e a) := by
  have hnear := ((continuous_frameBase g).comp
    (parallelFrameFlowMap_curve_continuous g 0 e)).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hc)
  filter_upwards [hnear] with s hs
  exact actualFullVariationPosition_eq_chart g o c e he a s hs

theorem actualFullVariationPosition_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ) :
    HasDerivAt (actualFullVariationPosition g o e a)
      (actualFullVariationVelocity g o e a t) t := by
  let c := (parallelFrameFlowMap g 0 t e).base
  have hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source :=
    mem_chart_source FourSpace c
  have h := (frameGeodesic_full_variation g o c e he a t hc).1.congr_of_eventuallyEq
    (actualFullVariationPosition_eventually_chart g o c e he a t hc)
  exact h.differentiableAt.hasDerivAt

theorem actualFullVariationVelocity_eq_chart (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ)
    (hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source) :
    actualFullVariationVelocity g o e a t =
      geodesicFrameVelocity g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) t := by
  exact ((frameGeodesic_full_variation g o c e he a t hc).1.congr_of_eventuallyEq
    (actualFullVariationPosition_eventually_chart g o c e he a t hc)).deriv

theorem actualFullVariationVelocity_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (e : FrameBundle g) (he : e ∈ o.positive)
    (a : CotangentCoordinates) (t : ℝ) :
    HasDerivAt (actualFullVariationVelocity g o e a)
      (-(Fin.cons 0 ((1 + frameCurvatureField g (parallelFrameFlowMap g 0 t e)) *ᵥ
        (fun i => actualFullVariationPosition g o e a t i.succ)))) t := by
  let c := (parallelFrameFlowMap g 0 t e).base
  have hc : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace c).source :=
    mem_chart_source FourSpace c
  have hnear := ((continuous_frameBase g).comp
    (parallelFrameFlowMap_curve_continuous g 0 e)).continuousAt.preimage_mem_nhds
      ((chartAt FourSpace c).open_source.mem_nhds hc)
  have heq : actualFullVariationVelocity g o e a =ᶠ[𝓝 t]
      geodesicFrameVelocity g c (parallelFrameFlowMap g 0 · e)
        (frameGeodesicCoordinateCurve g o c e) (frameGeodesicCoordinateVariation g o c e a) := by
    filter_upwards [hnear] with s hs
    exact actualFullVariationVelocity_eq_chart g o c e he a s hs
  have h := (frameGeodesic_full_variation g o c e he a t hc).2.congr_of_eventuallyEq heq
  rw [actualFullVariationPosition_eq_chart g o c e he a t hc]
  exact h

theorem actualFullVariation_initial (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (w : Fin 4 → ℝ) :
    actualFullVariationPosition g o e (frameFullInitialVariation g e w) 0 = 0 ∧
      actualFullVariationVelocity g o e (frameFullInitialVariation g e w) 0 = w := by
  let a := frameFullInitialVariation g e w
  let p := unitRadialCotangentState g e.base (frameUnitRadialState e)
  have hc : (parallelFrameFlowMap g 0 0 e).base ∈ (chartAt FourSpace e.base).source := by
    rw [parallelFrameFlowMap_zero]
    exact mem_chart_source FourSpace e.base
  have hp : p.1 ∈ (chartAt FourSpace e.base).target :=
    (chartAt FourSpace e.base).map_source (mem_chart_source FourSpace e.base)
  have hzero : frameKineticCurve g o e.base e 0 = p := by
    change unitRadialCotangentState g e.base
      (unitTangentRadialFlow g o 0 (frameUnitRadialState e)) = p
    rw [unitTangentRadialFlow_zero]
  have hvar : frameKineticVariation g o e.base e a 0 = a := by
    change fderiv ℝ (radialCoordinateFlow g o e.base e.base 0) p a = a
    rw [radialCoordinateFlow_self_zero_fderiv g o e.base (frameUnitRadialState e)
      (mem_chart_source FourSpace e.base)]
    rfl
  have hZ : frameGeodesicCoordinateVariation g o e.base e a 0 =
      fderiv ℝ (kineticVelocityCoordinates g e.base) p
        (0, WithLp.toLp 2 (metricInChart g e.base p.1 *ᵥ
          (frameChartMatrix g e.base (parallelFrameFlowMap g 0 0 e) *ᵥ w))) := by
    change fderiv ℝ (kineticVelocityCoordinates g e.base) (frameKineticCurve g o e.base e 0)
      (frameKineticVariation g o e.base e a 0) = _
    rw [hzero, hvar, parallelFrameFlowMap_zero]
    rfl
  have h := kinetic_frame_initial_data g e.base (parallelFrameFlowMap g 0 · e)
    (frameGeodesicCoordinateCurve g o e.base e)
    (frameGeodesicCoordinateVariation g o e.base e a) p w 0 hc hp hZ
  rw [actualFullVariationPosition_eq_chart g o e.base e he a 0 hc,
    actualFullVariationVelocity_eq_chart g o e.base e he a 0 hc]
  exact h

variable [T3Space M]

theorem actualFullVariation_eq_jacobi (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (w : Fin 4 → ℝ) (t : ℝ) :
    actualFullVariationPosition g o e (frameFullInitialVariation g e w) t =
        jacobiBlockMatrix t ((actualJacobiSolution g hRic e).J t) *ᵥ w ∧
      actualFullVariationVelocity g o e (frameFullInitialVariation g e w) t =
        jacobiBlockMatrix 1 ((actualJacobiSolution g hRic e).V t) *ᵥ w := by
  let a := frameFullInitialVariation g e w
  have hinit := actualFullVariation_initial g o e he w
  obtain ⟨K, hK⟩ := actualJacobiCurvature_bounded g hRic
  have hzero : (0 : ℝ) ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
    constructor <;> linarith [abs_nonneg t]
  have ht : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := by
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  exact Jacobi.full_jacobi_eq_mulVec (actualJacobiSolution g hRic e) K (hK e)
    (actualFullVariationPosition g o e a) (actualFullVariationVelocity g o e a)
    w _ _ hzero hinit.1 hinit.2
    (fun s _ => actualFullVariationPosition_hasDerivAt g o e he a s)
    (fun s _ => actualFullVariationVelocity_hasDerivAt g o e he a s) t ht

end
end PositiveEinsteinFour.Geometry
end


section

/-! The rough trace retains the alternating two-form slots. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem TwoFormSmooth.framedSecond_skew (hRic : RicciThree g) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (e : FrameBundle g) (i j k l : Fin 4) :
    twoFormFramedSecondDerivative o u e ![i,j,l,k] =
      -twoFormFramedSecondDerivative o u e ![i,j,k,l] := by
  let d := canonicalParallelMetricData g o hRic
  let γ := fun t => (d.flow i).map t e
  have hzero : γ 0 = e := actualParallelMetricData_zero g (canonicalFrameMeasure g o)
    (parallelFrameFlowMap_measurePreserving g o) hRic i e
  have hk := hu.framedCovariant_parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,l,k]
  have hj := (hu.framedCovariant_parallel_derivative γ 0 i
    (d.curve_continuous i e).continuousAt (d.parallelCurve i 0 e) ![j,k,l]).neg
  have heq : (fun t => -(twoFormFramedCovariantDerivative o u (γ t) ![j,k,l])) =
      fun t => twoFormFramedCovariantDerivative o u (γ t) ![j,l,k] := by
    funext t
    exact (hu.framedCovariant_skew hRic (γ t) j k l).symm
  change HasDerivAt (fun t => -(twoFormFramedCovariantDerivative o u (γ t) ![j,k,l]))
    (-twoFormFramedSecondDerivative o u (γ 0) (Fin.cons i ![j,k,l])) 0 at hj
  rw [heq] at hj
  have h := hk.unique hj
  rw [hzero] at h
  exact h

theorem TwoFormSmooth.roughTrace_skew (hRic : RicciThree g) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (e : FrameBundle g) (j k : Fin 4) :
    twoFormFramedRoughTrace o u e ![k,j] = -twoFormFramedRoughTrace o u e ![j,k] := by
  change (∑ i, twoFormFramedSecondDerivative o u e ![i,i,k,j]) =
    -(∑ i, twoFormFramedSecondDerivative o u e ![i,i,j,k])
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun i _ => hu.framedSecond_skew hRic e i i j k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exponential differential and its metric Jacobian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_rescaled_full_differential (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (d : M)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source)
    (w : Fin 4 → ℝ) :
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e))⁻¹ *ᵥ
      WithLp.ofLp (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
        (frameExponential g o e (t • v))) (coordinateVector 0) (WithLp.toLp 2 w)) =
      jacobiBlockMatrix t ((actualJacobiSolution g hRic e).J t) *ᵥ w := by
  let a := frameFullInitialVariation g e w
  have hc : e.base ∈ (chartAt FourSpace e.base).source := mem_chart_source FourSpace e.base
  have ha : ((0 : FourSpace →L[ℝ] FourSpace).prod (frameMomentumMap g e.base e))
      (WithLp.toLp 2 w) = a := by
    change (0, frameMomentumMap g e.base e (WithLp.toLp 2 w)) = a
    rw [frameMomentumMap_apply g e.base e hc]
    rfl
  rw [(frameExponential_rescaled_hasFDerivAt g o d e he t ht hd).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ha]
  have hchart := actualFullVariationPosition_eq_chart g o d e he a t hd
  change actualFullVariationPosition g o e a t =
    (frameChartMatrix g d (parallelFrameFlowMap g 0 t e))⁻¹ *ᵥ WithLp.ofLp
      (frameGeodesicCoordinateVariation g o d e a t).1 at hchart
  rw [frameGeodesicCoordinateVariation_fst g o d e he a t hd] at hchart
  exact hchart.symm.trans (actualFullVariation_eq_jacobi g o hRic e he w t).1

theorem frameExponential_rescaled_fderiv (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (d : M)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    fderiv ℝ (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e (t • v)))
      (coordinateVector 0) = Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
        (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
          jacobiBlockMatrix t ((actualJacobiSolution g hRic e).J t)) := by
  let E := frameChartMatrix g d (parallelFrameFlowMap g 0 t e)
  have hE : IsUnit E.det := Matrix.isUnit_det_of_left_inverse
    (frameChartMatrix_normalizes g d (parallelFrameFlowMap g 0 t e) hd)
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (fun w : Fin 4 → ℝ => E *ᵥ w)
    (frameExponential_rescaled_full_differential g o hRic d e he t ht hd (WithLp.ofLp v))
  change E *ᵥ (E⁻¹ *ᵥ WithLp.ofLp (fderiv ℝ
    (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e (t • v)))
      (coordinateVector 0) v)) = _ at h
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hE, Matrix.one_mulVec] at h
  apply (WithLp.ofLp_injective 2)
  exact h.trans (Matrix.mulVec_mulVec (WithLp.ofLp v) E _)

/-- The actual exponential differential at `t e₀`, written using the
parallel frame at its endpoint. -/
theorem frameExponential_hasFDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (d : M)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    HasFDerivAt (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e v))
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (frameChartMatrix g d (parallelFrameFlowMap g 0 t e) *
        jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t)))
      (t • coordinateVector 0) := by
  let E := frameChartMatrix g d (parallelFrameFlowMap g 0 t e)
  let J := (actualJacobiSolution g hRic e).J t
  have hres := (frameExponential_rescaled_hasFDerivAt g o d e he t ht hd).differentiableAt.hasFDerivAt
  rw [frameExponential_rescaled_fderiv g o hRic d e he t ht hd] at hres
  have hres' : HasFDerivAt
      (fun v : FourSpace => chartAt FourSpace d (frameExponential g o e (t • v)))
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * jacobiBlockMatrix t J))
      (t⁻¹ • (t • coordinateVector 0)) := by
    simpa only [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using hres
  have hs : HasFDerivAt (fun v : FourSpace => t⁻¹ • v)
      (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace) (t • coordinateVector 0) :=
    (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace).hasFDerivAt
  have h := hres'.comp (t • coordinateVector 0) hs
  have heq : (fun v : FourSpace => chartAt FourSpace d
      (frameExponential g o e (t • (t⁻¹ • v)))) =
      (fun v => chartAt FourSpace d (frameExponential g o e v)) := by
    funext v
    rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hD : (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * jacobiBlockMatrix t J)).comp
      (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace) =
      Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * jacobiBlockMatrix 1 (t⁻¹ • J)) := by
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id,
      ← map_smul, ← Matrix.mul_smul, jacobiBlockMatrix_rescale t ht.ne']
  change HasFDerivAt (fun v : FourSpace => chartAt FourSpace d
      (frameExponential g o e (t • (t⁻¹ • v))))
      ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ) (E * jacobiBlockMatrix t J)).comp
        (t⁻¹ • ContinuousLinearMap.id ℝ FourSpace)) (t • coordinateVector 0) at h
  rw [heq, hD] at h
  exact h

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

variable [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem TwoFormSmooth.roughTraceField_frame (hRic : RicciThree g) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (e : FrameBundle g) :
    twoFormFrameValue o (twoFormRoughTraceField o u) e =
      twoFormExtract (twoTensorMatrixLinear (twoFormFramedRoughTrace o u e)) := by
  let T := twoFormFramedRoughTrace o u ⟨e.base, o.frame e.base⟩
  have hT : twoFormTensor (twoFormExtract (twoTensorMatrixLinear T)) = T :=
    twoFormTensor_extract T (hu.roughTrace_skew hRic _)
  apply twoFormTensor_injective
  change twoFormTensor (twoFormFrameAction ((o.frame e.base).changeMatrix e.frame)
    (twoFormExtract (twoTensorMatrixLinear T))) = _
  rw [twoFormTensor_frameAction, hT]
  rw [twoFormTensor_extract _ (hu.roughTrace_skew hRic e)]
  exact (twoFormFramedRoughTrace_change u (o.frame e.base) e.frame).symm

theorem TwoFormSmooth.roughTrace (hRic : RicciThree g) {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) : TwoFormSmooth o (twoFormRoughTraceField o u) := by
  intro c S hS U _hU hUt _hp
  let F := fun z : FourSpace => twoFormTraceExtract
    (frameTensor (chartGramMatrix g c S z) (twoFormSecondCovariantCoordinates o u c z))
  have hF : ContDiffOn ℝ ∞ F U := by
    intro z hz
    exact (twoFormTraceExtract.contDiff.comp_contDiffAt z
      (hu.secondGram_contDiffAt c S z (hUt hz))).contDiffWithinAt
  apply hF.congr
  intro z hz
  rw [twoFormChartValue, dite_eq_left (hUt hz), hu.roughTraceField_frame hRic]
  have he := hu.framedSecond_chart c S hS ⟨z, hUt hz⟩
  exact congrArg twoFormTraceExtract he

def smoothTwoFormRoughTrace (hRic : RicciThree g) (u : smoothTwoForms o) : smoothTwoForms o :=
  ⟨twoFormRoughTraceField o u.val, u.property.roughTrace hRic⟩

theorem TwoFormSmooth.framedValue_roughTrace (hRic : RicciThree g)
    {u : M → TwoFormFour} (hu : TwoFormSmooth o u) (e : FrameBundle g) :
    twoFormFramedValue o (twoFormRoughTraceField o u) e =
      twoFormFramedRoughTrace o u e := by
  rw [twoFormFramedValue_eq, hu.roughTraceField_frame hRic,
    twoFormTensor_extract _ (hu.roughTrace_skew hRic e)]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constructed exponential is a C1 manifold map and satisfies the
radial Gauss identity, as a consequence of its actual differential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

/-- In output coordinates, the exponential differential has radial inner
product exactly equal to the initial radial component. -/
theorem frameExponential_chart_gauss (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (d : M) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source)
    (w : FourSpace) :
    (fun i => frameChartMatrix g d (parallelFrameFlowMap g 0 t e) i 0) ⬝ᵥ
      (metricInChart g d (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base) *ᵥ
        WithLp.ofLp (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
          (frameExponential g o e v)) (t • coordinateVector 0) w)) = w 0 := by
  let E := frameChartMatrix g d (parallelFrameFlowMap g 0 t e)
  let G := metricInChart g d (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base)
  let B := jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t)
  have hE : Eᵀ * G * E = 1 := frameChartMatrix_normalizes g d (parallelFrameFlowMap g 0 t e) hd
  rw [(frameExponential_hasFDerivAt g o hRic d e he t ht hd).fderiv]
  change (fun i => E i 0) ⬝ᵥ (G *ᵥ ((E * B) *ᵥ WithLp.ofLp w)) = w 0
  have hcol : (fun i => E i 0) = E *ᵥ Pi.single 0 1 := (Matrix.mulVec_single_one E 0).symm
  rw [hcol, ← Matrix.mulVec_mulVec, normalized_frame_pairing E G hE]
  change (Pi.single 0 1 : Fin 4 → ℝ) ⬝ᵥ (B *ᵥ WithLp.ofLp w) = w 0
  rw [show B = jacobiBlockMatrix 1 (t⁻¹ • (actualJacobiSolution g hRic e).J t) from rfl,
    jacobiBlockMatrix_mulVec]
  simp

end
end PositiveEinsteinFour.Geometry
end


section

/-! Intrinsic radial differential and Gauss identities for the actual
exponential, expressed in the metric rather than in an output chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Bundle
open scoped Manifold ContDiff _root_.Topology

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem chartBackwardOperator_center (x : M) :
    chartBackwardOperator x (chartAt FourSpace x x) =
      ContinuousLinearMap.id ℝ FourSpace := by
  have h := chartBackward_forward x x (mem_chart_source FourSpace x)
  rwa [chartForwardOperator_center, ContinuousLinearMap.comp_id] at h

theorem metricInChart_center_pairing (g : SmoothMetric M) (x : M)
    (u v : Fin 4 → ℝ) :
    u ⬝ᵥ (metricInChart g x (chartAt FourSpace x x) *ᵥ v) =
      g.inner x (WithLp.toLp 2 u) (WithLp.toLp 2 v) := by
  rw [metricInChart_pairing]
  change g.inner ((chartAt FourSpace x).symm (chartAt FourSpace x x))
    (chartBackwardOperator x (chartAt FourSpace x x) (WithLp.toLp 2 u))
    (chartBackwardOperator x (chartAt FourSpace x x) (WithLp.toLp 2 v)) = _
  rw [(chartAt FourSpace x).left_inv (mem_chart_source FourSpace x),
    chartBackwardOperator_center]
  rfl

variable [T3Space M] [CompactSpace M]

theorem frameExponential_gauss_first (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (t : ℝ) (ht : 0 < t) (w : FourSpace) :
    g.inner (parallelFrameFlowMap g 0 t e).base
      ((parallelFrameFlowMap g 0 t e).frame.vector 0)
      (mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) w) = w 0 := by
  let d := (parallelFrameFlowMap g 0 t e).base
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hx : frameExponential g o e (t • coordinateVector 0) = d :=
    frameExponential_first_ray g o e he t ht
  have hD := frameExponential_center_fderiv g o e (t • coordinateVector 0)
  rw [hx] at hD
  have hcol := frameChart_column_eq_derivative g d (parallelFrameFlowMap g 0 t e) 0 hd
  rw [chartForwardOperator_center] at hcol
  have hp := metricInChart_center_pairing g d
    (fun i => frameChartMatrix g d (parallelFrameFlowMap g 0 t e) i 0)
    (WithLp.ofLp (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
      (frameExponential g o e v)) (t • coordinateVector 0) w))
  rw [WithLp.toLp_ofLp, hcol, hD] at hp
  have hg := frameExponential_chart_gauss g o hRic d e he t ht hd w
  rw [hD] at hg
  exact hp.symm.trans hg

theorem frameExponential_radial_differential_first (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) :
    mfderiv I4 I4 (frameExponential g o e) (t • coordinateVector 0) (coordinateVector 0) =
      (parallelFrameFlowMap g 0 t e).frame.vector 0 := by
  let d := (parallelFrameFlowMap g 0 t e).base
  have hd : d ∈ (chartAt FourSpace d).source := mem_chart_source FourSpace d
  have hx : frameExponential g o e (t • coordinateVector 0) = d :=
    frameExponential_first_ray g o e he t ht
  have hD := frameExponential_center_fderiv g o e (t • coordinateVector 0)
  rw [hx] at hD
  rw [← hD, (frameExponential_hasFDerivAt g o hRic d e he t ht hd).fderiv]
  have hcol := frameChart_column_eq_derivative g d (parallelFrameFlowMap g 0 t e) 0 hd
  rw [chartForwardOperator_center] at hcol
  change WithLp.toLp 2 ((_ * _) *ᵥ WithLp.ofLp (coordinateVector 0)) = _
  rw [← Matrix.mulVec_mulVec, jacobiBlockMatrix_mulVec]
  have hb : (Fin.cons (1 * (coordinateVector 0 : FourSpace) 0)
      ((t⁻¹ • (actualJacobiSolution g hRic e).J t) *ᵥ
        (fun i => (coordinateVector 0 : FourSpace) i.succ)) : Fin 4 → ℝ) = Pi.single 0 1 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [coordinateVector]
    exact congrFun (Matrix.mulVec_zero (t⁻¹ • (actualJacobiSolution g hRic e).J t)) j
  rw [hb, Matrix.mulVec_single_one]
  exact hcol

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

/-- Gauss' lemma for every unit radial direction, derived from the actual
Jacobi differential and the proved orthogonal change of initial frame. -/
theorem frameExponential_gauss (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (q : Directions) (t : ℝ) (ht : 0 < t) (w : FourSpace) :
    g.inner (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) q.val)
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) w) = ⟪q.val, w⟫_ℝ := by
  let Q := directionOrientedMatrix q
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he (directionOrientedMatrix q)
  have hfirst : L (coordinateVector 0) = q.val := directionRotation_first q
  have htq : L (t • coordinateVector 0) = t • q.val := by rw [map_smul, hfirst]
  have hD (w : FourSpace) :
      mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0) w =
        mfderiv I4 I4 (frameExponential g o e) (t • q.val) (L w) := by
    have h := frameExponential_rotate_mfderiv g o e Q (t • coordinateVector 0) w
    change mfderiv I4 I4 (frameExponential g o f) (t • coordinateVector 0) w =
      mfderiv I4 I4 (frameExponential g o e) (L (t • coordinateVector 0)) (L w) at h
    rwa [htq] at h
  have hrad := frameExponential_radial_differential_first g o hRic f hf t ht
  rw [hD] at hrad
  change mfderiv I4 I4 (frameExponential g o e) (t • q.val)
    (L (coordinateVector 0)) = _ at hrad
  rw [hfirst] at hrad
  have hx : frameExponential g o e (t • q.val) = (parallelFrameFlowMap g 0 t f).base := by
    rw [← htq, ← frameExponential_rotate g o e Q]
    exact frameExponential_first_ray g o f hf t ht
  have h := frameExponential_gauss_first g o hRic f hf t ht (L.symm w)
  rw [hD] at h
  change g.inner (parallelFrameFlowMap g 0 t f).base
    ((parallelFrameFlowMap g 0 t f).frame.vector 0)
    (mfderiv I4 I4 (frameExponential g o e) (t • q.val) (L (L.symm w))) = _ at h
  rw [L.apply_symm_apply] at h
  have hinner := L.inner_map_map (coordinateVector 0) (L.symm w)
  rw [hfirst, L.apply_symm_apply] at hinner
  have hzero : ⟪(coordinateVector 0 : FourSpace), L.symm w⟫_ℝ = (L.symm w) 0 := by
    simp [PiLp.inner_apply, coordinateVector]
  let u : FourSpace := mfderiv I4 I4 (frameExponential g o e) (t • q.val) q.val
  let z : FourSpace := mfderiv I4 I4 (frameExponential g o e) (t • q.val) w
  change u = (parallelFrameFlowMap g 0 t f).frame.vector 0 at hrad
  change g.inner (frameExponential g o e (t • q.val)) u z = _
  rw [hrad, hx]
  exact h.trans (hinner.trans hzero).symm

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry05
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The six-dimensional action of the actual normal-frame connection. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatTwoFormConnection_radial (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (h : (∑ i : Fin 4, x i • heatNormalFrameConnection g c P i x) = 0) :
    (∑ i : Fin 4, x i • heatTwoFormConnection g c P i x) = 0 := by
  ext k l
  have he := congrArg (heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)) h
  simp only [map_sum, map_smul, map_zero, heatConnectionActionLinear_apply] at he
  have hk := congrArg (fun a : TwoFormFour => a k) he
  simpa only [heatTwoFormConnection, heatTwoFormConnectionMatrix, Matrix.sum_apply,
    Matrix.smul_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    PiLp.zero_apply, Matrix.zero_apply] using hk

variable [T2Space M] [CompactSpace M]

theorem HeatNormalFrameData.twoForm_connection_radial {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ Metric.ball 0 D.radius) :
    (∑ i : Fin 4, x i • heatTwoFormConnection g c D.point i x) = 0 :=
  heatTwoFormConnection_radial g c D.point x (D.radial_connection x hx)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite regularity of the actual two-form covariant expression in the
normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem heatTwoFormConnection_contDiffAt (n : ℕ) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ (n + 1) P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hdet : (P x).2.det ≠ 0) (i : Fin 4) (k l : Fin 6) :
    ContDiffAt ℝ n (fun y => heatTwoFormConnection g c P i y k l) x := by
  have hB : ContDiffAt ℝ n (heatNormalFrameConnection g c P i) x :=
    contDiffAt_pi.mpr (fun a => contDiffAt_pi.mpr
      (fun b => heatNormalFrameConnection_contDiffAt n g c P x hP hx hdet i a b))
  let L := (heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)).toContinuousLinearMap
  let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) k
  have hc := π.contDiff.contDiffAt.comp x (L.contDiff.contDiffAt.comp x hB)
  change ContDiffAt ℝ n
    (fun y => heatConnectionActionLinear (EuclideanSpace.basisFun (Fin 6) ℝ l)
      (heatNormalFrameConnection g c P i y) k) x at hc
  simpa only [heatConnectionActionLinear_apply, heatTwoFormConnection,
    heatTwoFormConnectionMatrix] using hc

theorem heatNormalTwoFormNabla_contDiffAt (n : ℕ) {o : FrameOrientation g}
    {u : M → TwoFormFour} (hu : TwoFormSmooth o u) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ (n + 1) P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hdet : (P x).2.det ≠ 0) (i : Fin 4) :
    ContDiffAt ℝ n (heatNormalTwoFormNabla o c P u i) x := by
  let a := heatNormalTwoFormValue o c P u
  have ha : ContDiffAt ℝ (n + 1) a x :=
    heatNormalTwoFormValue_contDiffAt (n + 1) hu c P x hP hx
  have ha0 : ContDiffAt ℝ n a x := ha.of_le (by exact_mod_cast Nat.le_succ n)
  have hal (l : Fin 6) : ContDiffAt ℝ n (fun y => a y l) x := by
    let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) l
    exact ContDiffAt.comp (f := a) (g := π) x π.contDiff.contDiffAt ha0
  have hproduct : ContDiffAt ℝ n
      (fun y => twoFormSkewAction (twoFormExtract (heatNormalFrameConnection g c P i y)) (a y)) x := by
    apply (contDiffAt_piLp 2).mpr
    intro k
    have hsum : ContDiffAt ℝ n (fun y => ∑ l : Fin 6, heatTwoFormConnection g c P i y k l * a y l) x :=
      ContDiffAt.sum (fun l _ => (heatTwoFormConnection_contDiffAt n c P x hP hx hdet i k l).mul
        (hal l))
    apply hsum.congr_of_eventuallyEq
    filter_upwards [] with y
    exact (congrFun (heatTwoFormConnectionMatrix_action (heatNormalFrameConnection g c P i y) (a y)) k).symm
  exact ((ha.fderiv_right (m := n) (by norm_num [Nat.cast_add])).clm_apply
    (contDiffAt_const (c := coordinateVector i))).add hproduct

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Bounded extension of the metric's actual curvature action to L2
two-forms. No bound on curvature is an additional input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

omit [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem twoFormCurvatureField_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (u : M → TwoFormFour) (x : M),
      ‖twoFormCurvatureField o u x‖ ≤ A * ‖u x‖ := by
  obtain ⟨C, hC, hb⟩ := twoFormMetricCurvatureTensor_bound g
  refine ⟨‖twoFormCurvatureOperator‖ * C,
    mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hC, fun u x => ?_⟩
  exact (twoFormCurvatureAction_norm_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hb ⟨x,o.frame x⟩)
        (ContinuousLinearMap.opNorm_nonneg _)) (norm_nonneg _))

def smoothL2CurvatureLinear : SmoothL2TwoForm o →ₗ[ℝ] SmoothL2TwoForm o where
  toFun u := smoothTwoFormCurvature (u : smoothTwoForms o)
  map_add' u v := by
    apply Subtype.ext
    funext x
    exact map_add (twoFormCurvatureLinear _) _ _
  map_smul' r u := by
    apply Subtype.ext
    funext x
    exact map_smul (twoFormCurvatureLinear _) r _

theorem smoothL2CurvatureLinear_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u : SmoothL2TwoForm o, ‖smoothL2CurvatureLinear u‖ ≤ A * ‖u‖ := by
  obtain ⟨A, hA, hb⟩ := twoFormCurvatureField_bound (o := o)
  refine ⟨A, hA, fun u => ?_⟩
  have hLp : ‖twoFormValueNormL2 (smoothL2CurvatureLinear u : smoothTwoForms o)‖ ≤
      A * ‖twoFormValueNormL2 (u : smoothTwoForms o)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [twoFormValueNormL2_coe (smoothL2CurvatureLinear u : smoothTwoForms o),
      twoFormValueNormL2_coe (u : smoothTwoForms o)] with x hv hu
    rw [hv, hu, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)]
    exact hb (u : smoothTwoForms o).val x
  calc
    _ = ‖twoFormValueNormL2 (smoothL2CurvatureLinear u : smoothTwoForms o)‖ :=
      (twoFormValueNormL2_eq_L2norm (smoothL2CurvatureLinear u)).symm
    _ ≤ A * ‖twoFormValueNormL2 (u : smoothTwoForms o)‖ := hLp
    _ = A * ‖u‖ := congrArg (A * ·) (twoFormValueNormL2_eq_L2norm u)

def twoFormCurvatureBound (o : FrameOrientation g) : ℝ :=
  Classical.choose (smoothL2CurvatureLinear_bound (o := o))

theorem smoothL2CurvatureLinear_norm_le (u : SmoothL2TwoForm o) :
    ‖smoothL2CurvatureLinear u‖ ≤ twoFormCurvatureBound o * ‖u‖ :=
  (Classical.choose_spec (smoothL2CurvatureLinear_bound (o := o))).2 u

def smoothL2Curvature : SmoothL2TwoForm o →L[ℝ] SmoothL2TwoForm o :=
  (smoothL2CurvatureLinear (o := o)).mkContinuous (twoFormCurvatureBound o)
    (fun u => smoothL2CurvatureLinear_norm_le u)

def twoFormL2Curvature : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  (smoothL2Curvature (o := o)).completion

/-- The bounded potential in `1 + ∇*∇ = 2 R - 5` for harmonic two-forms
when Ricci is normalized to `3g`. -/
def twoFormWeitzenbockPotential : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  (2 : ℝ) • twoFormL2Curvature - (5 : ℝ) • ContinuousLinearMap.id ℝ (TwoFormL2 o)

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

/-! Nondivergence form of a local scalar Laplace-type operator applied to
the actual Gaussian ansatz. The coefficients here are their values at the
point of evaluation; no equation or geometric coefficient identity is assumed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

def fourHeatConjugatedOperator (a : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 4 → ℝ)
    (c t : ℝ) (u : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  -(∑ i : Fin 4, ∑ j : Fin 4, a i j *
      (partialDeriv (partialDeriv u i) j x -
        (x i * partialDeriv u j x + x j * partialDeriv u i x) / (2 * t) +
        (x i * x j / (4 * t ^ 2) - (if i = j then 1 else 0) / (2 * t)) * u x)) +
    (∑ i : Fin 4, b i * (partialDeriv u i x - x i / (2 * t) * u x)) + c * u x

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exact eikonal and radial transport terms of the local Gaussian
ansatz, computed from the actual coordinate derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

def fourHeatRadialTransport (a : Matrix (Fin 4) (Fin 4) ℝ) (b : Fin 4 → ℝ)
    (u : FourSpace → ℝ) (x : FourSpace) : ℝ :=
  ((∑ i : Fin 4, ∑ j : Fin 4,
      a i j * (x i * partialDeriv u j x + x j * partialDeriv u i x)) +
    ((∑ i : Fin 4, a i i) - 4 - ∑ i : Fin 4, b i * x i) * u x) / 2

theorem fourHeatConjugatedOperator_decomposition (a : Matrix (Fin 4) (Fin 4) ℝ)
    (b : Fin 4 → ℝ) (c t : ℝ) (u : FourSpace → ℝ) (x : FourSpace) :
    (‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t) * u x +
      fourHeatConjugatedOperator a b c t u x =
      fourHeatLocalOperator a b c u x + fourHeatRadialTransport a b u x / t +
        fourHeatEikonalDefect a x / t ^ 2 * u x := by
  unfold fourHeatConjugatedOperator fourHeatLocalOperator fourHeatRadialTransport
    fourHeatEikonalDefect
  norm_num [Fin.sum_univ_four]
  ring

theorem fourHeatEikonalDefect_zero (a : Matrix (Fin 4) (Fin 4) ℝ) (x : FourSpace)
    (h : ∀ i : Fin 4, (∑ j : Fin 4, a i j * x j) = x i) :
    fourHeatEikonalDefect a x = 0 := by
  have hq : (∑ i : Fin 4, ∑ j : Fin 4, a i j * x i * x j) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = x i * ∑ j : Fin 4, a i j * x j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = x i ^ 2 := by rw [h]; ring
  simp only [fourHeatEikonalDefect, hq, sub_self, zero_div]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Gaussian ansatz identities with precisely the local regularity
needed at the point of evaluation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped ContDiff BigOperators

noncomputable section

theorem fourHeatGaussian_amplitude_partial_at (t : ℝ) (ht : t ≠ 0)
    (u : FourSpace → ℝ) (x : FourSpace) (hu : DifferentiableAt ℝ u x) (i : Fin 4) :
    partialDeriv (fun y => fourHeatGaussian t y * u y) i x =
      fourHeatGaussian t x * (partialDeriv u i x - x i / (2 * t) * u x) := by
  rw [scalar_partial_product _ _ x
    ((fourHeatGaussian_smooth t).differentiable (by simp)).differentiableAt hu i,
    fourHeatGaussian_partial t ht]
  ring

theorem fourHeatGaussian_amplitude_second_at (t : ℝ) (ht : t ≠ 0)
    (u : FourSpace → ℝ) (x : FourSpace) (hu : ContDiffAt ℝ 2 u x) (i j : Fin 4) :
    partialDeriv (partialDeriv (fun y => fourHeatGaussian t y * u y) i) j x =
      fourHeatGaussian t x *
        (partialDeriv (partialDeriv u i) j x -
          (x i * partialDeriv u j x + x j * partialDeriv u i x) / (2 * t) +
          (x i * x j / (4 * t ^ 2) - (if i = j then 1 else 0) / (2 * t)) * u x) := by
  rw [scalar_partial_second_product_at (fourHeatGaussian t) u x
    ((fourHeatGaussian_smooth t).contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hu i j,
    fourHeatGaussian_partial_partial t ht,
    fourHeatGaussian_partial t ht, fourHeatGaussian_partial t ht]
  ring

theorem fourHeatLocalOperator_gaussian_at (a : Matrix (Fin 4) (Fin 4) ℝ)
    (b : Fin 4 → ℝ) (c t : ℝ) (ht : t ≠ 0)
    (u : FourSpace → ℝ) (x : FourSpace) (hu : ContDiffAt ℝ 2 u x) :
    fourHeatLocalOperator a b c (fun y => fourHeatGaussian t y * u y) x =
      fourHeatGaussian t x * fourHeatConjugatedOperator a b c t u x := by
  unfold fourHeatLocalOperator fourHeatConjugatedOperator
  simp_rw [fourHeatGaussian_amplitude_second_at t ht u x hu,
    fourHeatGaussian_amplitude_partial_at t ht u x (hu.differentiableAt (by norm_num))]
  let K := fourHeatGaussian t x
  let Q := fun i j : Fin 4 => partialDeriv (partialDeriv u i) j x -
    (x i * partialDeriv u j x + x j * partialDeriv u i x) / (2 * t) +
    (x i * x j / (4 * t ^ 2) - (if i = j then 1 else 0) / (2 * t)) * u x
  let P := fun i : Fin 4 => partialDeriv u i x - x i / (2 * t) * u x
  change -(∑ i, ∑ j, a i j * (K * Q i j)) + (∑ i, b i * (K * P i)) + c * (K * u x) =
    K * (-(∑ i, ∑ j, a i j * Q i j) + (∑ i, b i * P i) + c * u x)
  have hQ : (∑ i, ∑ j, a i j * (K * Q i j)) = K * ∑ i, ∑ j, a i j * Q i j := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hP : (∑ i, b i * (K * P i)) = K * ∑ i, b i * P i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hQ, hP]
  ring

theorem fourHeatLocalOperator_transport_residual_at (a : Matrix (Fin 4) (Fin 4) ℝ)
    (b : Fin 4 → ℝ) (c t : ℝ) (ht : 0 < t)
    (u : FourSpace → ℝ) (x : FourSpace) (hu : ContDiffAt ℝ 2 u x) :
    deriv (fun s => fourHeatGaussian s x * u x) t +
      fourHeatLocalOperator a b c (fun y => fourHeatGaussian t y * u y) x =
      fourHeatGaussian t x *
        (fourHeatLocalOperator a b c u x + fourHeatRadialTransport a b u x / t +
          fourHeatEikonalDefect a x / t ^ 2 * u x) := by
  rw [(fourHeatGaussian_amplitude_time t ht u x).deriv,
    fourHeatLocalOperator_gaussian_at a b c t ht.ne' u x hu]
  have h := fourHeatConjugatedOperator_decomposition a b c t u x
  calc
    _ = fourHeatGaussian t x * ((‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t) * u x +
        fourHeatConjugatedOperator a b c t u x) := by ring
    _ = _ := congrArg (fourHeatGaussian t x * ·) h

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

theorem fourHeatRadialTransport_of_radial (a : Mat4) (b : Fin 4 → ℝ)
    (u : FourSpace → ℝ) (x : FourSpace)
    (hrow : ∀ i, ∑ j : Fin 4, a i j * x j = x i)
    (hcol : ∀ j, ∑ i : Fin 4, a i j * x i = x j) :
    fourHeatRadialTransport a b u x =
      fderiv ℝ u x x + ((∑ i : Fin 4, a i i) - 4 - ∑ i : Fin 4, b i * x i) / 2 * u x := by
  have hsum : (∑ i : Fin 4, ∑ j : Fin 4,
      a i j * (x i * partialDeriv u j x + x j * partialDeriv u i x)) =
      (∑ j : Fin 4, (∑ i : Fin 4, a i j * x i) * partialDeriv u j x) +
        ∑ i : Fin 4, (∑ j : Fin 4, a i j * x j) * partialDeriv u i x := by
    norm_num [Fin.sum_univ_four]
    ring
  rw [fourHeatRadialTransport, hsum]
  simp_rw [hrow, hcol]
  rw [fourHeat_radial_derivative]
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The radial identity for the actual exponential pullback metric,
and the resulting cancellation of the Gaussian eikonal defect. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix
open scoped Manifold ContDiff _root_.Topology InnerProductSpace BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalMetric_gauss_vector (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (v w : FourSpace) (hv : v ≠ 0) :
    g.inner (frameExponential g o e v)
      (mfderiv I4 I4 (frameExponential g o e) v v)
      (mfderiv I4 I4 (frameExponential g o e) v w) = inner ℝ v w := by
  let q : Directions := ⟨‖v‖⁻¹ • v, by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvq : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  have hg := frameExponential_gauss g o hRic e he q ‖v‖ hr w
  rw [hvq] at hg
  let D : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (frameExponential g o e) v
  let B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ := g.inner (frameExponential g o e v)
  have hD : D v = ‖v‖ • D q.val := by
    calc
      D v = D (‖v‖ • q.val) := congrArg D hvq.symm
      _ = _ := D.map_smul _ _
  change B (D q.val) (D w) = inner ℝ q.val w at hg
  change B (D v) (D w) = inner ℝ v w
  rw [hD, map_smul, _root_.smul_apply, smul_eq_mul, hg]
  rw [← real_inner_smul_left, hvq]

theorem heatNormalMetric_radial (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace) :
    heatNormalMetric g o e v *ᵥ WithLp.ofLp v = WithLp.ofLp v := by
  by_cases hv : v = 0
  · subst v
    simp
  ext i
  rw [heatNormalMetric_row, g.symm,
    heatNormalMetric_gauss_vector g o hRic e he v (coordinateVector i) hv]
  have hb : coordinateVector i = (EuclideanSpace.basisFun (Fin 4) ℝ) i := by
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  rw [hb, EuclideanSpace.inner_basisFun_real]

theorem heatNormalMetric_inverse_radial (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hdet : (heatNormalMetric g o e v).det ≠ 0) :
    (heatNormalMetric g o e v)⁻¹ *ᵥ WithLp.ofLp v = WithLp.ofLp v := by
  calc
    _ = (heatNormalMetric g o e v)⁻¹ *ᵥ
        (heatNormalMetric g o e v *ᵥ WithLp.ofLp v) := by
      rw [heatNormalMetric_radial g o hRic e he]
    _ = ((heatNormalMetric g o e v)⁻¹ * heatNormalMetric g o e v) *ᵥ WithLp.ofLp v :=
      mulVec_mulVec _ _ _
    _ = _ := by rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]

theorem heatNormalMetric_eikonal (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive) (v : FourSpace)
    (hdet : (heatNormalMetric g o e v).det ≠ 0) :
    fourHeatEikonalDefect (heatNormalMetric g o e v)⁻¹ v = 0 := by
  apply fourHeatEikonalDefect_zero
  intro i
  exact congrFun (heatNormalMetric_inverse_radial g o hRic e he v hdet) i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The leading scalar heat transport equation in density divergence form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped _root_.Topology BigOperators

noncomputable section

theorem fourHeatDensity_leading_transport (a : FourSpace → Mat4) (J u : FourSpace → ℝ)
    (x : FourSpace) (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hJ : DifferentiableAt ℝ J x) (hu : DifferentiableAt ℝ u x)
    (hrad : ∀ᶠ y in 𝓝 x, ∀ i, ∑ j : Fin 4, a y i j * y j = y i)
    (hcol : ∀ j, ∑ i : Fin 4, a x i j * x i = x j)
    (hnorm : ∀ᶠ y in 𝓝 x, u y ^ 2 * J y = 1) :
    fourHeatRadialTransport (a x) (fourHeatDensityDrift a J x) u x = 0 := by
  rw [fourHeatRadialTransport_of_radial (a x) _ u x hrad.self_of_nhds hcol,
    fourHeatDensityDrift_radial a J x ha hrad]
  have hn := fourHeat_normalized_amplitude_radial J u x hJ hu hnorm
  convert hn using 1
  all_goals try with_reducible_and_instances rfl
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The local four-component heat operator in a radial frame. The additional
first-order Gaussian term vanishes by the radial connection identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatOneFirst_gaussian (B : Fin 4 → Mat4)
    (t : ℝ) (ht : t ≠ 0) (u : FourSpace → Fin 4 → ℝ) (x : FourSpace)
    (hu : ∀ l, DifferentiableAt ℝ (fun y => u y l) x)
    (hB : ∀ k l, (∑ i : Fin 4, x i * B i k l) = 0) (k : Fin 4) :
    fourHeatOneFirst B (fun y l => fourHeatGaussian t y * u y l) x k =
      fourHeatGaussian t x * fourHeatOneFirst B u x k := by
  have hz : (∑ i : Fin 4, ∑ l : Fin 4, x i * B i k l * u x l) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hB]
    simp
  unfold fourHeatOneFirst
  simp_rw [fourHeatGaussian_amplitude_partial_at t ht _ x (hu _)]
  have he (i : Fin 4) (l : Fin 4) :
      B i k l * (fourHeatGaussian t x *
        (partialDeriv (fun y => u y l) i x - x i / (2 * t) * u x l)) =
      fourHeatGaussian t x * (B i k l * partialDeriv (fun y => u y l) i x) -
        (fourHeatGaussian t x / (2 * t)) * (x i * B i k l * u x l) := by ring
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hz]
  ring

theorem fourHeatOneOperator_transport_residual_at (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (t : ℝ) (ht : 0 < t)
    (u : FourSpace → Fin 4 → ℝ) (x : FourSpace)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x)
    (hB : ∀ k l, (∑ i : Fin 4, x i * B i k l) = 0) (k : Fin 4) :
    deriv (fun s => fourHeatGaussian s x * u x k) t +
      fourHeatOneOperator a b B C (fun y l => fourHeatGaussian t y * u y l) x k =
    fourHeatGaussian t x *
      (fourHeatOneOperator a b B C u x k +
        fourHeatRadialTransport a b (fun y => u y k) x / t +
        fourHeatEikonalDefect a x / t ^ 2 * u x k) := by
  unfold fourHeatOneOperator
  rw [fourHeatOneFirst_gaussian B t ht.ne' u x
      (fun l => (hu l).differentiableAt (by norm_num)) hB,
    fourHeatOneZero_gaussian]
  have hs := fourHeatLocalOperator_transport_residual_at a b 0 t ht
    (fun y => u y k) x (hu k)
  linarith

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

theorem fourHeatRadialAverage_transport (m : ℕ) (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 1 f) (x : FourSpace) :
    fderiv ℝ (fourHeatRadialAverage m f) x x +
      (m + 1 : ℝ) * fourHeatRadialAverage m f x = f x := by
  let P : ℝ → ℝ := fun s => s ^ (m + 1) * f (s • x)
  have hpath : ContDiff ℝ 1 P :=
    (contDiff_id.pow (m + 1)).mul
      (hf.comp (contDiff_id.smul (contDiff_const (c := x))))
  have hderiv (s : ℝ) : deriv P s =
      (m + 1 : ℝ) * (s ^ m * f (s • x)) +
        fourHeatRadialAverageDerivative m f x s x := by
    have hs : HasDerivAt (fun t : ℝ => t • x) x s := by
      have h := (ContinuousLinearMap.toSpanSingleton ℝ x).hasFDerivAt.comp_hasDerivAt
        s (hasDerivAt_id s)
      simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, Function.comp_def,
        id_eq] using! h
    have hc := ((hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt).comp_hasDerivAt s hs
    have hd := ((hasDerivAt_pow (m + 1) s).mul hc).deriv
    change deriv P s = _ at hd
    rw [hd]
    simp only [fourHeatRadialAverageDerivative, _root_.smul_apply, smul_eq_mul,
      Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Function.comp_def]
    ring
  have hD : Continuous (fourHeatRadialAverageDerivative m f x) :=
    (fourHeatRadialAverageDerivative_continuous m f hf).comp
      (continuous_const.prodMk continuous_id)
  have hF : Continuous (fun s : ℝ => s ^ m * f (s • x)) :=
    (continuous_id.pow m).mul (hf.continuous.comp (continuous_id.smul continuous_const))
  have hI := intervalIntegral.integral_deriv_of_contDiffOn_Icc hpath.contDiffOn
    (by norm_num : (0 : ℝ) ≤ 1)
  simp_rw [hderiv] at hI
  rw [intervalIntegral.integral_add
    ((hF.const_mul _).intervalIntegrable 0 1)
    ((hD.clm_apply continuous_const).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul,
    ← ContinuousLinearMap.intervalIntegral_apply (hD.intervalIntegrable 0 1) x] at hI
  have hP1 : P 1 = f x := by simp [P]
  have hP0 : P 0 = 0 := by simp [P]
  rw [hP1, hP0, sub_zero] at hI
  rw [(fourHeatRadialAverage_hasFDerivAt m f hf x).fderiv]
  exact (add_comm _ _).trans hI

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

theorem fourHeatRadialTransport_product (a : Mat4) (b : Fin 4 → ℝ)
    (U V : FourSpace → ℝ) (x : FourSpace)
    (hrow : ∀ i, ∑ j : Fin 4, a i j * x j = x i)
    (hcol : ∀ j, ∑ i : Fin 4, a i j * x i = x j)
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x) :
    fourHeatRadialTransport a b (fun y => U y * V y) x =
      U x * fderiv ℝ V x x + V x * fourHeatRadialTransport a b U x := by
  rw [fourHeatRadialTransport_of_radial a b _ x hrow hcol,
    fourHeatRadialTransport_of_radial a b U x hrow hcol,
    fderiv_fun_mul hU hV]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

theorem fourHeatWeightedRadialAverage_transport (m : ℕ) (a : Mat4) (b : Fin 4 → ℝ)
    (U F : FourSpace → ℝ) (x : FourSpace)
    (hU : ContDiff ℝ 1 U) (hF : ContDiff ℝ 1 F) (hU0 : ∀ y, U y ≠ 0)
    (hrow : ∀ i, ∑ j : Fin 4, a i j * x j = x i)
    (hcol : ∀ j, ∑ i : Fin 4, a i j * x i = x j)
    (hTU : fourHeatRadialTransport a b U x = 0) :
    fourHeatRadialTransport a b (fourHeatWeightedRadialAverage m U F) x +
      (m + 1 : ℝ) * fourHeatWeightedRadialAverage m U F x = F x := by
  let Q := fun y => F y / U y
  have hQ : ContDiff ℝ 1 Q := hF.div hU hU0
  have hV : DifferentiableAt ℝ (fourHeatRadialAverage m Q) x :=
    (fourHeatRadialAverage_hasFDerivAt m Q hQ x).differentiableAt
  change fourHeatRadialTransport a b (fun y => U y * fourHeatRadialAverage m Q y) x +
    (m + 1 : ℝ) * (U x * fourHeatRadialAverage m Q x) = F x
  rw [fourHeatRadialTransport_product a b U _ x hrow hcol
    ((hU.differentiable one_ne_zero).differentiableAt) hV, hTU, mul_zero, add_zero]
  calc
    _ = U x * (fderiv ℝ (fourHeatRadialAverage m Q) x x +
        (m + 1 : ℝ) * fourHeatRadialAverage m Q x) := by ring
    _ = U x * Q x := by rw [fourHeatRadialAverage_transport m Q hQ x]
    _ = F x := by exact mul_div_cancel₀ (F x) (hU0 x)

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

theorem fourHeatCoefficient_transport (m : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ) (c U : FourSpace → ℝ)
    (x : FourSpace) (hU : ContDiff ℝ 1 U) (hU0 : ∀ y, U y ≠ 0)
    (ha : ∀ i j, ContDiff ℝ 1 (fun y => a y i j))
    (hb : ∀ i, ContDiff ℝ 1 (fun y => b y i)) (hc : ContDiff ℝ 1 c)
    (hm : ContDiff ℝ 3 (fourHeatCoefficient a b c U m))
    (hrow : ∀ i, ∑ j : Fin 4, a x i j * x j = x i)
    (hcol : ∀ j, ∑ i : Fin 4, a x i j * x i = x j)
    (hTU : fourHeatRadialTransport (a x) (b x) U x = 0) :
    fourHeatRadialTransport (a x) (b x) (fourHeatCoefficient a b c U (m + 1)) x +
      (m + 1 : ℝ) * fourHeatCoefficient a b c U (m + 1) x =
        -fourHeatLocalOperator (a x) (b x) (c x) (fourHeatCoefficient a b c U m) x := by
  apply fourHeatWeightedRadialAverage_transport m (a x) (b x) U _ x hU _ hU0
    hrow hcol hTU
  exact (fourHeatLocalOperator_contDiff 1 a b c _ ha hb hc hm).neg

end
end PositiveEinsteinFour.Geometry
end


section

/-! Locality of the coefficient operator through its actual second
derivatives. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped _root_.Topology

noncomputable section

theorem fourHeatBundleOperator_germ (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6)
    {u v : FourSpace → Fin 6 → ℝ} {x : FourSpace}
    (h : ∀ q, (fun y => u y q) =ᶠ[𝓝 x] fun y => v y q) (k : Fin 6) :
    fourHeatBundleOperator a b B C u x k = fourHeatBundleOperator a b B C v x k := by
  simp only [fourHeatBundleOperator, fourHeatLocalOperator_germ a b 0 (h k),
    fourHeatBundleFirst, fourHeatBundleZero, fourHeat_partial_germ (h _),
    fun q => (h q).self_of_nhds]

theorem fourHeatBundleOperator_zero_of_locally_zero (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → HeatMat6) (C : HeatMat6) {u : FourSpace → Fin 6 → ℝ} {x : FourSpace}
    (h : ∀ q, (fun y => u y q) =ᶠ[𝓝 x] fun _ => (0 : ℝ)) (k : Fin 6) :
    fourHeatBundleOperator a b B C u x k = 0 := by
  rw [fourHeatBundleOperator_germ a b B C h k]
  have hp (i : Fin 4) : partialDeriv (fun _ : FourSpace => (0 : ℝ)) i = fun _ => 0 := by
    funext y
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  simp only [fourHeatBundleOperator, fourHeatBundleFirst, fourHeatBundleZero,
    fourHeatLocalOperator, hp]
  simp only [mul_zero, Finset.sum_const_zero, neg_zero, add_zero]

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

theorem fourHeatRadialTransport_const_mul (a : Mat4) (b : Fin 4 → ℝ) (r : ℝ)
    (u : FourSpace → ℝ) (x : FourSpace) :
    fourHeatRadialTransport a b (fun y => r * u y) x =
      r * fourHeatRadialTransport a b u x := by
  unfold fourHeatRadialTransport
  simp only [fourHeat_partial_const_mul, Fin.sum_univ_four]
  ring

theorem fourHeatRadialTransport_add (a : Mat4) (b : Fin 4 → ℝ)
    (u v : FourSpace → ℝ) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (x : FourSpace) :
    fourHeatRadialTransport a b (fun y => u y + v y) x =
      fourHeatRadialTransport a b u x + fourHeatRadialTransport a b v x := by
  unfold fourHeatRadialTransport
  simp only [fourHeat_partial_add u v x hu.differentiableAt hv.differentiableAt,
    Fin.sum_univ_four]
  ring

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

theorem fourHeatPolynomial_operator (a : Mat4) (b : Fin 4 → ℝ) (c : ℝ)
    (u : Fin 4 → FourSpace → ℝ) (hu : ∀ i, ContDiff ℝ 2 (u i)) (t : ℝ) (x : FourSpace) :
    fourHeatLocalOperator a b c (fourHeatPolynomial u t) x =
      fourHeatLocalOperator a b c (u 0) x + t * fourHeatLocalOperator a b c (u 1) x +
        t ^ 2 * fourHeatLocalOperator a b c (u 2) x +
        t ^ 3 * fourHeatLocalOperator a b c (u 3) x := by
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  have h3 := hu 3
  unfold fourHeatPolynomial
  rw [fourHeatLocalOperator_add a b c _ _ (by fun_prop) (by fun_prop),
    fourHeatLocalOperator_add a b c _ _ (by fun_prop) (by fun_prop),
    fourHeatLocalOperator_add a b c _ _ h0 (by fun_prop)]
  simp only [fourHeatLocalOperator_const_mul]

theorem fourHeatPolynomial_transport (a : Mat4) (b : Fin 4 → ℝ)
    (u : Fin 4 → FourSpace → ℝ) (hu : ∀ i, ContDiff ℝ 2 (u i)) (t : ℝ) (x : FourSpace) :
    fourHeatRadialTransport a b (fourHeatPolynomial u t) x =
      fourHeatRadialTransport a b (u 0) x + t * fourHeatRadialTransport a b (u 1) x +
        t ^ 2 * fourHeatRadialTransport a b (u 2) x +
        t ^ 3 * fourHeatRadialTransport a b (u 3) x := by
  have h0 : Differentiable ℝ (u 0) := (hu 0).differentiable (by norm_num)
  have h1 : Differentiable ℝ (u 1) := (hu 1).differentiable (by norm_num)
  have h2 : Differentiable ℝ (u 2) := (hu 2).differentiable (by norm_num)
  have h3 : Differentiable ℝ (u 3) := (hu 3).differentiable (by norm_num)
  unfold fourHeatPolynomial
  rw [fourHeatRadialTransport_add a b _ _ (by fun_prop) (by fun_prop),
    fourHeatRadialTransport_add a b _ _ (by fun_prop) (by fun_prop),
    fourHeatRadialTransport_add a b _ _ h0 (by fun_prop)]
  simp only [fourHeatRadialTransport_const_mul]

theorem fourHeatPolynomial_gaussian_residual (a : Mat4) (b : Fin 4 → ℝ) (c : ℝ)
    (u : Fin 4 → FourSpace → ℝ) (hu : ∀ i, ContDiff ℝ 2 (u i))
    (t : ℝ) (ht : 0 < t) (x : FourSpace)
    (hE : fourHeatEikonalDefect a x = 0)
    (h0 : fourHeatRadialTransport a b (u 0) x = 0)
    (h1 : fourHeatRadialTransport a b (u 1) x + u 1 x =
      -fourHeatLocalOperator a b c (u 0) x)
    (h2 : fourHeatRadialTransport a b (u 2) x + 2 * u 2 x =
      -fourHeatLocalOperator a b c (u 1) x)
    (h3 : fourHeatRadialTransport a b (u 3) x + 3 * u 3 x =
      -fourHeatLocalOperator a b c (u 2) x) :
    deriv (fun s => fourHeatGaussian s x * fourHeatPolynomial u s x) t +
      fourHeatLocalOperator a b c (fun y => fourHeatGaussian t y * fourHeatPolynomial u t y) x =
      fourHeatGaussian t x * t ^ 3 * fourHeatLocalOperator a b c (u 3) x := by
  have hd := (fourHeatGaussian_hasDerivAt_time t ht x).mul
    (fourHeatPolynomial_hasDerivAt u t x)
  change HasDerivAt (fun s => fourHeatGaussian s x * fourHeatPolynomial u s x) _ t at hd
  have hr := fourHeatLocalOperator_transport_residual_at a b c t ht
    (fourHeatPolynomial u t) x (fourHeatPolynomial_contDiff u hu t).contDiffAt
  rw [(fourHeatGaussian_amplitude_time t ht (fourHeatPolynomial u t) x).deriv,
    hE, zero_div, zero_mul, add_zero] at hr
  rw [fourHeatPolynomial_operator a b c u hu t x,
    fourHeatPolynomial_transport a b u hu t x, h0] at hr
  have h1' : fourHeatRadialTransport a b (u 1) x =
      -fourHeatLocalOperator a b c (u 0) x - u 1 x := by linarith only [h1]
  have h2' : fourHeatRadialTransport a b (u 2) x =
      -fourHeatLocalOperator a b c (u 1) x - 2 * u 2 x := by linarith only [h2]
  have h3' : fourHeatRadialTransport a b (u 3) x =
      -fourHeatLocalOperator a b c (u 2) x - 3 * u 3 x := by linarith only [h3]
  rw [h1', h2', h3'] at hr
  rw [hd.deriv]
  calc
    _ = fourHeatGaussian t x * (‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t) *
          fourHeatPolynomial u t x +
        fourHeatLocalOperator a b c (fun y => fourHeatGaussian t y * fourHeatPolynomial u t y) x +
        fourHeatGaussian t x * (u 1 x + 2 * t * u 2 x + 3 * t ^ 2 * u 3 x) := by ring
    _ = _ := by rw [hr]; field_simp [ht.ne']; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact spatial slices of the lower order family coefficients. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatDensityDrift_germ {a a' : FourSpace → Mat4} {J J' : FourSpace → ℝ}
    {x : FourSpace} (ha : a =ᶠ[𝓝 x] a') (hJ : J =ᶠ[𝓝 x] J') :
    fourHeatDensityDrift a J x = fourHeatDensityDrift a' J' x := by
  have hpartial (i j : Fin 4) : partialDeriv (fun y => a y i j) i x =
      partialDeriv (fun y => a' y i j) i x :=
    fourHeat_partial_germ (ha.mono fun y hy => congrArg (fun A : Mat4 => A i j) hy) i
  funext j
  simp only [fourHeatDensityDrift, hpartial, fourHeat_partial_germ hJ,
    ha.self_of_nhds, hJ.self_of_nhds]

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

theorem HeatNormalFrameData.bundleFirst_radial {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace)
    (hx : x ∈ ball 0 D.radius) (hdet : (heatNormalMetric g o e x).det ≠ 0) :
    (∑ i : Fin 4, x i • heatNormalBundleFirst D x i) = 0 := by
  apply fourHeatConnectionFirst_radial
  · intro j
    have hrow := congrFun (heatNormalMetric_inverse_radial g o hRic e he x hdet) j
    have hs (i : Fin 4) : (heatNormalMetric g o e x)⁻¹ i j =
        (heatNormalMetric g o e x)⁻¹ j i :=
      congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    simpa only [Matrix.mulVec, dotProduct, hs] using hrow
  · exact D.twoForm_connection_radial x hx

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

theorem HeatNormalFrameData.oneFirst_radial {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace)
    (hx : x ∈ ball 0 D.radius) (hdet : (heatNormalMetric g o e x).det ≠ 0) :
    (∑ i : Fin 4, x i • heatNormalOneFirst D x i) = 0 := by
  apply fourHeatOneConnectionFirst_radial
  · intro j
    have hrow := congrFun (heatNormalMetric_inverse_radial g o hRic e he x hdet) j
    have hs (i : Fin 4) : (heatNormalMetric g o e x)⁻¹ i j =
        (heatNormalMetric g o e x)⁻¹ j i :=
      congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    simpa only [Matrix.mulVec, dotProduct, hs] using hrow
  · exact D.radial_connection x hx

end
end PositiveEinsteinFour.Geometry
end


section

/-! Values and curvature potentials in the actual normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M]

theorem HeatNormalFrameData.value_as_actual {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (u : M → TwoFormFour) (x : FourSpace) (hx : x ∈ ball 0 D.radius) :
    heatNormalTwoFormValue o c D.point u x = twoFormFrameValue o u (D.frame x hx) := by
  apply twoFormTensor_injective
  rw [heatNormalTwoFormValue_tensor, ← twoFormFramedValue_eq]
  have h := heat_framedValue_chart o u c (D.frame x hx)
    ((chartAt FourSpace c).map_target (D.in_chart x hx))
  have hm : frameChartMatrix g c (D.frame x hx) = (D.point x).2 :=
    frameChartMatrix_chartFrameState g c
      ⟨D.point x, D.in_chart x hx, D.orthonormal x hx⟩
  have hb : chartAt FourSpace c (D.frame x hx).base = (D.point x).1 :=
    (chartAt FourSpace c).right_inv (D.in_chart x hx)
  rw [hm, hb] at h
  exact h.symm

theorem HeatNormalFrameData.potential_action_as_actual {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (u : M → TwoFormFour) (x : FourSpace) (hx : x ∈ ball 0 D.radius) :
    WithLp.toLp 2 (heatNormalPotential g c D.point x *ᵥ
      WithLp.ofLp (heatNormalTwoFormValue o c D.point u x)) =
      (6 : ℝ) • twoFormFrameValue o u (D.frame x hx) -
        (2 : ℝ) • twoFormFrameValue o (twoFormCurvatureField o u) (D.frame x hx) := by
  rw [D.potential_as_actual x hx, D.value_as_actual u x hx,
    twoFormCurvatureField_frame]
  apply twoFormPotentialMatrix_apply
  intro i j k l
  simp only [twoFormMetricCurvatureTensor, frameTensor_curvatureCoordinates]
  exact frame_algebraic_lastSkew (D.frame x hx).frame i j k l

end
end PositiveEinsteinFour.Geometry
end


section

/-! The compact weak solution operator for one plus the rough two-form
Laplacian, defined by the actual H1 and L2 pairings. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormRoughSolution : TwoFormL2 o →L[ℝ] TwoFormH1 o :=
  (twoFormH1ToL2 (o := o)).adjoint

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

theorem fourHeatBundleCoefficient_transport (m : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → HeatMat6) (C : FourSpace → HeatMat6) (U : FourSpace → ℝ)
    (x : FourSpace) (hU : ContDiff ℝ 1 U) (hU0 : ∀ y, U y ≠ 0)
    (ha : ∀ i j, ContDiff ℝ 1 (fun y => a y i j))
    (hb : ∀ i, ContDiff ℝ 1 (fun y => b y i))
    (hB : ∀ i k l, ContDiff ℝ 1 (fun y => B y i k l))
    (hC : ∀ k l, ContDiff ℝ 1 (fun y => C y k l))
    (hm : ∀ k l, ContDiff ℝ 3 (fun y => fourHeatBundleCoefficient a b B C U m y k l))
    (hrow : ∀ i, ∑ j : Fin 4, a x i j * x j = x i)
    (hcol : ∀ j, ∑ i : Fin 4, a x i j * x i = x j)
    (hTU : fourHeatRadialTransport (a x) (b x) U x = 0) (k l : Fin 6) :
    fourHeatRadialTransport (a x) (b x)
        (fun y => fourHeatBundleCoefficient a b B C U (m + 1) y k l) x +
      (m + 1 : ℝ) * fourHeatBundleCoefficient a b B C U (m + 1) x k l =
    -fourHeatBundleOperator (a x) (b x) (B x) (C x)
      (fun y q => fourHeatBundleCoefficient a b B C U m y q l) x k := by
  apply fourHeatWeightedRadialAverage_transport m (a x) (b x) U _ x hU _ hU0
    hrow hcol hTU
  exact (fourHeatBundleOperator_contDiff 1 a b B C _ ha hb hB hC
    (fun q => hm q l) k).neg

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

theorem fourHeatOneCoefficient_transport (m : ℕ)
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → Mat4) (C : FourSpace → Mat4) (U : FourSpace → ℝ)
    (x : FourSpace) (hU : ContDiff ℝ 1 U) (hU0 : ∀ y, U y ≠ 0)
    (ha : ∀ i j, ContDiff ℝ 1 (fun y => a y i j))
    (hb : ∀ i, ContDiff ℝ 1 (fun y => b y i))
    (hB : ∀ i k l, ContDiff ℝ 1 (fun y => B y i k l))
    (hC : ∀ k l, ContDiff ℝ 1 (fun y => C y k l))
    (hm : ∀ k l, ContDiff ℝ 3 (fun y => fourHeatOneCoefficient a b B C U m y k l))
    (hrow : ∀ i, ∑ j : Fin 4, a x i j * x j = x i)
    (hcol : ∀ j, ∑ i : Fin 4, a x i j * x i = x j)
    (hTU : fourHeatRadialTransport (a x) (b x) U x = 0) (k l : Fin 4) :
    fourHeatRadialTransport (a x) (b x)
        (fun y => fourHeatOneCoefficient a b B C U (m + 1) y k l) x +
      (m + 1 : ℝ) * fourHeatOneCoefficient a b B C U (m + 1) x k l =
    -fourHeatOneOperator (a x) (b x) (B x) (C x)
      (fun y q => fourHeatOneCoefficient a b B C U m y q l) x k := by
  apply fourHeatWeightedRadialAverage_transport m (a x) (b x) U _ x hU _ hU0
    hrow hcol hTU
  exact (fourHeatOneOperator_contDiff 1 a b B C _ ha hb hB hC
    (fun q => hm q l) k).neg

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity and finite time polynomials for the actual four-component
differential expression. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatOneOperator_const_mul (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (r : ℝ)
    (u : FourSpace → Fin 4 → ℝ) (x : FourSpace) (k : Fin 4) :
    fourHeatOneOperator a b B C (fun y l => r * u y l) x k =
      r * fourHeatOneOperator a b B C u x k := by
  unfold fourHeatOneOperator fourHeatOneFirst fourHeatOneZero
  simp only [fourHeatLocalOperator_const_mul, fourHeat_partial_const_mul]
  have hB : (∑ i : Fin 4, ∑ l : Fin 4,
      B i k l * (r * partialDeriv (fun y => u y l) i x)) =
      r * (∑ i : Fin 4, ∑ l : Fin 4, B i k l * partialDeriv (fun y => u y l) i x) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hC : (∑ l : Fin 4, C k l * (r * u x l)) =
      r * (∑ l : Fin 4, C k l * u x l) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hB, hC]
  ring

theorem fourHeatOnePolynomial_operator (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4)
    (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (hu : ∀ m k, ContDiff ℝ 2 (fun x => u m x k)) (t : ℝ) (x : FourSpace) (k : Fin 4) :
    fourHeatOneOperator a b B C (fourHeatOnePolynomial u t) x k =
      fourHeatOneOperator a b B C (u 0) x k +
        t * fourHeatOneOperator a b B C (u 1) x k +
        t ^ 2 * fourHeatOneOperator a b B C (u 2) x k +
        t ^ 3 * fourHeatOneOperator a b B C (u 3) x k := by
  have h0 := hu 0
  have h1 := hu 1
  have h2 := hu 2
  have h3 := hu 3
  unfold fourHeatOnePolynomial fourHeatPolynomial
  rw [fourHeatOneOperator_add a b B C _ _
      (fun l => ((h0 l).add (contDiff_const.mul (h1 l))).add (contDiff_const.mul (h2 l)))
      (fun l => contDiff_const.mul (h3 l)),
    fourHeatOneOperator_add a b B C _ _
      (fun l => (h0 l).add (contDiff_const.mul (h1 l)))
      (fun l => contDiff_const.mul (h2 l)),
    fourHeatOneOperator_add a b B C _ _ h0 (fun l => contDiff_const.mul (h1 l))]
  simp only [fourHeatOneOperator_const_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact cancellation of the first four matrix heat amplitudes. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped BigOperators ContDiff

noncomputable section

theorem fourHeatOnePolynomial_gaussian_residual (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4)
    (u : Fin 4 → FourSpace → Fin 4 → ℝ)
    (hu : ∀ i k, ContDiff ℝ 2 (fun y => u i y k))
    (t : ℝ) (ht : 0 < t) (x : FourSpace)
    (hB : ∀ k l, (∑ i : Fin 4, x i * B i k l) = 0)
    (hE : fourHeatEikonalDefect a x = 0)
    (h0 : ∀ k, fourHeatRadialTransport a b (fun y => u 0 y k) x = 0)
    (h1 : ∀ k, fourHeatRadialTransport a b (fun y => u 1 y k) x + u 1 x k =
      -fourHeatOneOperator a b B C (u 0) x k)
    (h2 : ∀ k, fourHeatRadialTransport a b (fun y => u 2 y k) x + 2 * u 2 x k =
      -fourHeatOneOperator a b B C (u 1) x k)
    (h3 : ∀ k, fourHeatRadialTransport a b (fun y => u 3 y k) x + 3 * u 3 x k =
      -fourHeatOneOperator a b B C (u 2) x k) (k : Fin 4) :
    deriv (fun s => fourHeatGaussian s x * fourHeatOnePolynomial u s x k) t +
      fourHeatOneOperator a b B C
        (fun y l => fourHeatGaussian t y * fourHeatOnePolynomial u t y l) x k =
      fourHeatGaussian t x * t ^ 3 * fourHeatOneOperator a b B C (u 3) x k := by
  have hP (l : Fin 4) : ContDiff ℝ 2 (fun y => fourHeatOnePolynomial u t y l) :=
    fourHeatPolynomial_contDiff (fun m y => u m y l) (fun m => hu m l) t
  have hd := (fourHeatGaussian_hasDerivAt_time t ht x).mul
    (fourHeatPolynomial_hasDerivAt (fun m y => u m y k) t x)
  change HasDerivAt (fun s => fourHeatGaussian s x * fourHeatOnePolynomial u s x k) _ t at hd
  have hr := fourHeatOneOperator_transport_residual_at a b B C t ht
    (fourHeatOnePolynomial u t) x (fun l => (hP l).contDiffAt) hB k
  rw [(fourHeatGaussian_amplitude_time t ht (fun y => fourHeatOnePolynomial u t y k) x).deriv,
    hE, zero_div, zero_mul, add_zero] at hr
  rw [fourHeatOnePolynomial_operator a b B C u hu t x k] at hr
  have hT := fourHeatPolynomial_transport a b (fun m y => u m y k) (fun m => hu m k) t x
  change fourHeatRadialTransport a b (fun y => fourHeatOnePolynomial u t y k) x = _ at hT
  rw [hT, h0] at hr
  have h1' : fourHeatRadialTransport a b (fun y => u 1 y k) x =
      -fourHeatOneOperator a b B C (u 0) x k - u 1 x k := by linarith only [h1 k]
  have h2' : fourHeatRadialTransport a b (fun y => u 2 y k) x =
      -fourHeatOneOperator a b B C (u 1) x k - 2 * u 2 x k := by linarith only [h2 k]
  have h3' : fourHeatRadialTransport a b (fun y => u 3 y k) x =
      -fourHeatOneOperator a b B C (u 2) x k - 3 * u 3 x k := by linarith only [h3 k]
  rw [h1', h2', h3'] at hr
  rw [hd.deriv]
  calc
    _ = fourHeatGaussian t x * (‖x‖ ^ 2 / (4 * t ^ 2) - 2 / t) *
          fourHeatOnePolynomial u t x k +
        fourHeatOneOperator a b B C
          (fun y l => fourHeatGaussian t y * fourHeatOnePolynomial u t y l) x k +
        fourHeatGaussian t x * (u 1 x k + 2 * t * u 2 x k + 3 * t ^ 2 * u 3 x k) := by
          dsimp only [fourHeatOnePolynomial]
          ring
    _ = _ := by rw [hr]; field_simp [ht.ne']; ring

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

theorem HeatNormalOneExtension.amplitude_zero {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g} {D : HeatNormalFrameData g o c e}
    (E : HeatNormalOneExtension D) (x : FourSpace) :
    E.amplitude 0 x = E.base.U x • (1 : Mat4) := by
  ext k l
  simp only [HeatNormalOneExtension.amplitude, fourHeatOneCoefficient,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Hodge operator becomes invertible after adding its
finite harmonic projection. This is the needed Fredholm step. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormHodgeCompact : TwoFormH1 o →L[ℝ] TwoFormH1 o :=
  twoFormRoughSolution.comp (twoFormWeitzenbockPotential.comp twoFormH1ToL2)

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates07
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual smooth Hodge Laplacian in the normalization Ric = 3g. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def smoothHodgeLaplacian (hRic : RicciThree g) (u : smoothTwoForms o) : smoothTwoForms o :=
  (6 : ℝ) • u - (2 : ℝ) • smoothTwoFormCurvature u - smoothTwoFormRoughTrace hRic u

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

/-! Locality of the covariant coefficient operator, including where the
amplitude vanishes outside the normal chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped _root_.Topology

noncomputable section

theorem fourHeatCovariantDerivative_germ (A : Fin 4 → FourSpace → HeatMat6)
    {u v : FourSpace → Fin 6 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun y => v y k) (i : Fin 4) (k : Fin 6) :
    fourHeatCovariantDerivative A u i x k = fourHeatCovariantDerivative A v i x k := by
  simp only [fourHeatCovariantDerivative, fourHeat_partial_germ (h k),
    fun l => (h l).self_of_nhds]

theorem fourHeatCovariantOperator_germ (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6)
    {u v : FourSpace → Fin 6 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun y => v y k) (k : Fin 6) :
    fourHeatCovariantOperator a b A V u x k = fourHeatCovariantOperator a b A V v x k := by
  have hD (i : Fin 4) (l : Fin 6) :
      (fun y => fourHeatCovariantDerivative A u i y l) =ᶠ[𝓝 x]
        fun y => fourHeatCovariantDerivative A v i y l := by
    have hn := eventually_all.mpr fun q => (h q).eventuallyEq_nhds
    filter_upwards [hn] with y hy
    exact fourHeatCovariantDerivative_germ A hy i l
  simp only [fourHeatCovariantOperator, fourHeatCovariantDerivative_germ A (hD _),
    fourHeatCovariantDerivative_germ A h, fun l => (h l).self_of_nhds]

theorem fourHeatCovariantOperator_zero_of_locally_zero (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → HeatMat6) (V : HeatMat6)
    {u : FourSpace → Fin 6 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun _ => (0 : ℝ)) (k : Fin 6) :
    fourHeatCovariantOperator a b A V u x k = 0 := by
  rw [fourHeatCovariantOperator_germ a b A V h k]
  have hD (i : Fin 4) : fourHeatCovariantDerivative A (fun _ _ => 0) i = fun _ _ => 0 := by
    funext y l
    simp only [fourHeatCovariantDerivative, partialDeriv, fderiv_const_apply,
      _root_.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [fourHeatCovariantOperator, hD, mul_zero, Finset.sum_const_zero,
    neg_zero, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Locality of the actual four-component covector heat operator. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Filter
open scoped _root_.Topology
noncomputable section

theorem fourHeatOneOperator_zero_of_locally_zero (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) {u : FourSpace → Fin 4 → ℝ} {x : FourSpace}
    (h : ∀ q, (fun y => u y q) =ᶠ[𝓝 x] fun _ => (0 : ℝ)) (k : Fin 4) :
    fourHeatOneOperator a b B C u x k = 0 := by
  rw [fourHeatOneOperator_germ a b B C h k]
  have hp (i : Fin 4) : partialDeriv (fun _ : FourSpace => (0 : ℝ)) i = fun _ => 0 := by
    funext y
    simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]
  simp only [fourHeatOneOperator, fourHeatOneFirst, fourHeatOneZero,
    fourHeatLocalOperator, hp]
  simp only [mul_zero, Finset.sum_const_zero, neg_zero, add_zero]

theorem fourHeatOneCovariantDerivative_germ (A : Fin 4 → FourSpace → Mat4)
    {u v : FourSpace → Fin 4 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun y => v y k) (i : Fin 4) (k : Fin 4) :
    fourHeatOneCovariantDerivative A u i x k = fourHeatOneCovariantDerivative A v i x k := by
  simp only [fourHeatOneCovariantDerivative, fourHeat_partial_germ (h k),
    fun l => (h l).self_of_nhds]

theorem fourHeatOneCovariantOperator_germ (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → Mat4) (V : Mat4)
    {u v : FourSpace → Fin 4 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun y => v y k) (k : Fin 4) :
    fourHeatOneCovariantOperator a b A V u x k = fourHeatOneCovariantOperator a b A V v x k := by
  have hD (i : Fin 4) (l : Fin 4) :
      (fun y => fourHeatOneCovariantDerivative A u i y l) =ᶠ[𝓝 x]
        fun y => fourHeatOneCovariantDerivative A v i y l := by
    have hn := eventually_all.mpr fun q => (h q).eventuallyEq_nhds
    filter_upwards [hn] with y hy
    exact fourHeatOneCovariantDerivative_germ A hy i l
  simp only [fourHeatOneCovariantOperator, fourHeatOneCovariantDerivative_germ A (hD _),
    fourHeatOneCovariantDerivative_germ A h, fun l => (h l).self_of_nhds]

theorem fourHeatOneCovariantOperator_zero_of_locally_zero (a : Mat4) (b : Fin 4 → ℝ)
    (A : Fin 4 → FourSpace → Mat4) (V : Mat4)
    {u : FourSpace → Fin 4 → ℝ} {x : FourSpace}
    (h : ∀ k, (fun y => u y k) =ᶠ[𝓝 x] fun _ => (0 : ℝ)) (k : Fin 4) :
    fourHeatOneCovariantOperator a b A V u x k = 0 := by
  rw [fourHeatOneCovariantOperator_germ a b A V h k]
  have hD (i : Fin 4) : fourHeatOneCovariantDerivative A (fun _ _ => 0) i = fun _ _ => 0 := by
    funext y l
    simp only [fourHeatOneCovariantDerivative, partialDeriv, fderiv_const_apply,
      _root_.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  simp only [fourHeatOneCovariantOperator, hD, mul_zero, Finset.sum_const_zero,
    neg_zero, add_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The smooth Hodge Laplacian agrees pointwise with the covariant
component expression for dδ + δd. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHodgeLaplacian_framed (hRic : RicciThree g)
    (u : smoothTwoForms o) (e : FrameBundle g) :
    twoFormFramedValue o (smoothHodgeLaplacian hRic u).val e =
      (6 : ℝ) • twoFormFramedValue o u.val e -
        (2 : ℝ) • twoFormFramedValue o (smoothTwoFormCurvature u).val e -
          twoFormFramedRoughTrace o u.val e := by
  let L : smoothTwoForms o →ₗ[ℝ] CovariantCoordinates 2 :=
    { toFun w := twoFormTensorLinear
        (twoFormFrameActionLinear ((o.frame e.base).changeMatrix e.frame) (w.val e.base))
      map_add' w v := by simp only [Submodule.coe_add, Pi.add_apply, map_add]
      map_smul' r w := by simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply] }
  have hL (w : smoothTwoForms o) : L w = twoFormFramedValue o w.val e :=
    (twoFormFramedValue_eq o w.val e).symm
  calc
    _ = L (smoothHodgeLaplacian hRic u) := (hL _).symm
    _ = (6 : ℝ) • L u - (2 : ℝ) • L (smoothTwoFormCurvature u) -
        L (smoothTwoFormRoughTrace hRic u) := by
      rw [smoothHodgeLaplacian, map_sub, map_sub, map_smul, map_smul]
    _ = _ := by
      rw [hL, hL, hL]
      exact congrArg (fun T : CovariantCoordinates 2 =>
        (6 : ℝ) • twoFormFramedValue o u.val e -
          (2 : ℝ) • twoFormFramedValue o (smoothTwoFormCurvature u).val e - T)
        (u.property.framedValue_roughTrace hRic e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual compact resolvent of one plus the two-form Hodge
Laplacian, constructed from the proved nonnegative weak Hodge form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormShiftedHodgeCompact : TwoFormH1 o →L[ℝ] TwoFormH1 o :=
  twoFormHodgeCompact - twoFormRoughSolution.comp twoFormH1ToL2

def twoFormShiftedHodge : TwoFormH1 o →L[ℝ] TwoFormH1 o :=
  ContinuousLinearMap.id ℝ (TwoFormH1 o) - twoFormShiftedHodgeCompact

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

theorem heatNormalOneOperatorAmplitude_regular (E : HeatNormalOneExtension D)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 4 a) :
    ContDiff ℝ 2 (heatNormalOneOperatorAmplitude E a) := by
  apply (contDiff_piLp (p := 2)).mpr
  intro k
  apply fourHeatOneOperator_contDiff 2 E.base.a E.base.b E.B E.C
  · exact fun i j => (E.base.a_regular i j).of_le (by norm_num)
  · exact fun i => (E.base.b_regular i).of_le (by norm_num)
  · exact fun i k l => (E.B_regular i k l).of_le (by norm_num)
  · exact fun k l => (E.C_regular k l).of_le (by norm_num)
  · intro l
    exact (contDiff_piLp (p := 2)).mp ha l

theorem heatNormalOneOperatorAmplitude_support (E : HeatNormalOneExtension D)
    (a : FourSpace → FourSpace) :
    tsupport (heatNormalOneOperatorAmplitude E a) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport a)
  intro x hx
  by_contra hn
  have hz : a =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hn] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hk (k : Fin 4) : (fun y => a y k) =ᶠ[𝓝 x] (fun _ => 0) :=
    hz.mono fun y hy => by change a y k = 0; rw [hy]; rfl
  apply hx
  apply WithLp.ofLp_injective 2
  funext k
  exact fourHeatOneOperator_zero_of_locally_zero (E.base.a x) (E.base.b x) (E.B x)
    (E.C x) hk k


end
end PositiveEinsteinFour.Geometry
end


section

/-! First and second normal tensor derivatives agree with the six scalar
covariant derivatives used in the bundle parametrix. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem heatNormal_tensor_second {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (P : FourSpace → CoordinateFrameSpace)
    (x : FourSpace) (hP : ContDiffAt ℝ 2 P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i j : Fin 4) :
    tensorCovariantDirection (heatNormalFrameConnection g c P)
      (tensorCovariantDirection (heatNormalFrameConnection g c P)
        (fun y => frameTensor (P y).2 (twoFormCoordinates o u c (P y).1)) i) j x =
      twoFormTensor (WithLp.toLp 2 (fun k => fourHeatCovariantDerivative
        (heatTwoFormConnection g c P)
        (fourHeatCovariantDerivative (heatTwoFormConnection g c P)
          (fun y k => heatNormalTwoFormValue o c P u y k) i) j x k)) := by
  have hP1 := hP.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hp : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 1 P y := hP1.eventually (by norm_num)
  have ht : ∀ᶠ y in 𝓝 x, (P y).1 ∈ (chartAt FourSpace c).target :=
    hP.continuousAt.fst.preimage_mem_nhds ((chartAt FourSpace c).open_target.mem_nhds hx)
  have hfirst : tensorCovariantDirection (heatNormalFrameConnection g c P)
      (fun y => frameTensor (P y).2 (twoFormCoordinates o u c (P y).1)) i =ᶠ[𝓝 x]
      (fun y => twoFormTensor (heatNormalTwoFormNabla o c P u i y)) := by
    filter_upwards [hp, ht, hG.eventually_nhds] with y hpy hty hgy
    exact heatNormal_tensor_first hu c P y hpy hty hgy i
  rw [heat_covariant_congr (heatNormalFrameConnection g c P) _ _ x hfirst j]
  have hdet : (P x).2.det ≠ 0 := by
    intro hz
    have h := congrArg Matrix.det hG.self_of_nhds
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul, Matrix.det_one] at h
    norm_num at h
  have hn := (heatNormalTwoFormNabla_contDiffAt 1 hu c P x hP hx hdet i).differentiableAt
    one_ne_zero
  rw [heat_twoForm_covariant_tensor (heatNormalFrameConnection g c P)
    (heatNormalTwoFormNabla o c P u i) x hn j
    (heatNormalFrameConnection_skew g c P x (hP.differentiableAt (by norm_num)) hx hG j)]
  have he : (fun y k => heatNormalTwoFormNabla o c P u i y k) =ᶠ[𝓝 x]
      fourHeatCovariantDerivative (heatTwoFormConnection g c P)
        (fun y k => heatNormalTwoFormValue o c P u y k) i := by
    filter_upwards [hp, ht] with y hpy hty
    funext k
    exact heatNormalTwoFormNabla_component hu c P y hpy hty i k
  apply congrArg twoFormTensor
  apply congrArg (WithLp.toLp 2)
  funext k
  exact heat_fourCovariant_congr (heatTwoFormConnection g c P) _ _ x he j k

end
end PositiveEinsteinFour.Geometry
end


section

/-! Uniform compact bounds for the one-form transport amplitudes and residual. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

def HeatFamilyOneCoefficients.lastCoefficient (E : HeatFamilyOneCoefficients)
    (z : HeatRadialFrameSpace) (k l : Fin 4) : ℝ :=
  heatFamilyOneOperator E.base.a E.base.b E.B E.C (fun y q => E.amplitude 3 y q l) z k


end
end PositiveEinsteinFour.Geometry
end


section

/-! Compact bounds for scalar amplitudes and the remaining transport coefficient. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Metric
open scoped ContDiff BigOperators Matrix.Norms.Elementwise
noncomputable section

def HeatFamilySmoothCoefficients.scalarLastCoefficient (E : HeatFamilySmoothCoefficients)
    (z : HeatRadialFrameSpace) : ℝ :=
  heatFamilyScalarOperator E.a E.b (E.scalarAmplitude 3) z

end
end PositiveEinsteinFour.Geometry
end


section

/-! The differential operator in the actual bundle parametrix agrees
with the global smooth Hodge Laplacian in the constructed normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Metric Filter
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

theorem heat_smoothHodge_frameValue {g : SmoothMetric M} {o : FrameOrientation g}
    (hRic : RicciThree g) (u : smoothTwoForms o) (e : FrameBundle g) :
    twoFormFrameValue o (smoothHodgeLaplacian hRic u).val e =
      (6 : ℝ) • twoFormFrameValue o u.val e -
        (2 : ℝ) • twoFormFrameValue o (twoFormCurvatureField o u.val) e -
          twoFormFrameValue o (twoFormRoughTraceField o u.val) e := by
  let L := twoFormExtractLinear.comp twoTensorMatrixLinear
  have hl (a : TwoFormFour) : L (twoFormTensor a) = a := heat_extract_twoFormTensor a
  have h := smoothHodgeLaplacian_framed hRic u e
  rw [← u.property.framedValue_roughTrace hRic e] at h
  simp only [twoFormFramedValue_eq] at h
  have he := congrArg L h
  simpa only [map_sub, map_smul, hl, smoothTwoFormCurvature] using he

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual transport identities hold on the entire common normal ball,
not only on a separately chosen germ for each initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.transport (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r) :
    (∀ i, ∑ j : Fin 4, N.extension.base.a x i j * x j = x i) ∧
    (∀ j, ∑ i : Fin 4, N.extension.base.a x i j * x i = x j) ∧
    fourHeatEikonalDefect (N.extension.base.a x) x = 0 ∧
    fourHeatRadialTransport (N.extension.base.a x) (N.extension.base.b x)
      N.extension.base.U x = 0 ∧
    (∀ k l, (∑ i : Fin 4, x i * N.extension.B x i k l) = 0) := by
  let A := N.extension
  let J := frameExponentialJacobian g o e
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ ball (0 : FourSpace) r := isOpen_ball.mem_nhds hx
  have ha : A.base.a =ᶠ[𝓝 x] (fun y => (heatNormalMetric g o e y)⁻¹) := by
    filter_upwards [hnear] with y hy
    exact (N.actual y hy).1
  have hnorm : ∀ᶠ y in 𝓝 x, A.base.U y ^ 2 * J y = 1 := by
    filter_upwards [hnear] with y hy
    rw [(N.actual y hy).2.2.2.2]
    exact heatNormalLeadingAmplitude_normalization g o e y
      (Real.sqrt_pos.mpr (N.metric_pos y hy))
  have hJg : J =ᶠ[𝓝 x] (fun y => (A.base.U y ^ 2)⁻¹) := by
    filter_upwards [hnorm] with y hy
    exact eq_inv_of_mul_eq_one_right hy
  have hJ : DifferentiableAt ℝ J x :=
    (((A.base.U_regular.differentiable (by norm_num) x).pow 2).inv
      (pow_ne_zero 2 (A.base.U_pos x).ne')).congr_of_eventuallyEq hJg
  have hrad : ∀ᶠ y in 𝓝 x, ∀ i, ∑ j : Fin 4, A.base.a y i j * y j = y i := by
    filter_upwards [hnear] with y hy i
    rw [(N.actual y hy).1]
    exact congrFun (heatNormalMetric_inverse_radial g o hRic e he y (N.metric_pos y hy).ne') i
  have hcol (j : Fin 4) : ∑ i : Fin 4, A.base.a x i j * x i = x j := by
    have hs (i : Fin 4) : A.base.a x i j = A.base.a x j i := by
      rw [ha.self_of_nhds]
      exact congrFun (congrFun (heatNormalInverse_symm g o e x) j) i
    simp_rw [hs]
    exact hrad.self_of_nhds j
  refine ⟨hrad.self_of_nhds, hcol, ?_, ?_, ?_⟩
  · rw [ha.self_of_nhds]
    exact heatNormalMetric_eikonal g o hRic e he x (N.metric_pos x hx).ne'
  · have hb : A.base.b x = fourHeatDensityDrift A.base.a J x := by
      rw [(N.actual x hx).2.1]
      exact (fourHeatDensityDrift_germ ha Filter.EventuallyEq.rfl).symm
    rw [hb]
    exact fourHeatDensity_leading_transport A.base.a J A.base.U x
      (fun i j => (A.base.a_regular i j).differentiable (by norm_num) x) hJ
      (A.base.U_regular.differentiable (by norm_num) x) hrad hcol hnorm
  · intro k l
    rw [(N.actual x hx).2.2.1]
    have hh := N.frameData.bundleFirst_radial hRic he x
      (ball_subset_ball N.radius_le hx) (N.metric_pos x hx).ne'
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
      using congrArg (fun B : HeatMat6 => B k l) hh

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

theorem HeatNormalFrameData.actual_rough_components_at {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (hRic : RicciThree g)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (hpx : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hd : 0 < (heatNormalMetric g o e x).det) :
    ∀ (u : M → TwoFormFour), TwoFormSmooth o u → ∀ k : Fin 6,
      -(∑ i, ∑ j, (heatNormalMetric g o e x)⁻¹ i j *
        fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
          (fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
            (fun y l => heatNormalTwoFormValue o c D.point u y l) i) j x k) +
        (∑ i, heatNormalDrift g o e x i *
          fourHeatCovariantDerivative (heatTwoFormConnection g c D.point)
            (fun y l => heatNormalTwoFormValue o c D.point u y l) i x k) =
        -twoFormFrameValue o (twoFormRoughTraceField o u) (D.frame x hx) k := by
  have hgx : ∀ᶠ y in 𝓝 x,
      (D.point y).2ᵀ * metricInChart g c (D.point y).1 * (D.point y).2 = 1 := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact D.orthonormal y hy
  have hr := D.actual_tensor_rough_at x hx hpx hs hd
  intro u hu k
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
      using hr u hu v
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

theorem HeatNormalFrameData.actual_bundle_operator_at {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    (D : HeatNormalFrameData g o c e) (hRic : RicciThree g)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (hpx : ContDiffAt ℝ 2 D.point x)
    (hs : frameExponential g o e x ∈ (chartAt FourSpace c).source)
    (hdet : 0 < (heatNormalMetric g o e x).det) :
    ∀ (u : smoothTwoForms o), ∀ k : Fin 6,
      fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalBundleFirst D x) (heatNormalBundleZero D x)
        (fun y l => heatNormalTwoFormValue o c D.point u.val y l) x k =
      heatNormalTwoFormValue o c D.point (smoothHodgeLaplacian hRic u).val x k := by
  have hr := D.actual_rough_components_at hRic x hx hpx hs hdet
  intro u k
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
  rw [hr u.val u.property k, D.value_as_actual _ x hx, heat_smoothHodge_frameValue hRic u (D.frame x hx)]
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

/-! The residual of every member of the common family is the same jointly
continuous last transport coefficient, times its explicit Gaussian factor. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.amplitude_transport (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (m : ℕ) (hm : m ≤ 2) (k l : Fin 6) :
    fourHeatRadialTransport (N.extension.base.a x) (N.extension.base.b x)
      (fun y => N.extension.amplitude (m + 1) y k l) x +
      (m + 1 : ℝ) * N.extension.amplitude (m + 1) x k l =
    -fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
      (N.extension.B x) (N.extension.C x) (fun y q => N.extension.amplitude m y q l) x k := by
  obtain ⟨hrow, hcol, _, hU, _⟩ := N.transport hRic he x hx
  exact fourHeatBundleCoefficient_transport m _ _ _ _ _ x
    (N.extension.base.U_regular.of_le (by norm_num)) (fun y => (N.extension.base.U_pos y).ne')
    (fun i j => (N.extension.base.a_regular i j).of_le (by norm_num))
    (fun i => (N.extension.base.b_regular i).of_le (by norm_num))
    (fun i k l => (N.extension.B_regular i k l).of_le (by norm_num))
    (fun k l => (N.extension.C_regular k l).of_le (by norm_num))
    (fun k l => (N.extension.amplitude_regular m (by omega) k l).of_le (by norm_num))
    hrow hcol hU k l

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

/-! The adjoint of the actual isometric frame realization reconstructs one-form
L2 sections from continuous frame data. -/

namespace PositiveEinsteinFour.Geometry
open EinsteinFour MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_18
theorem oneFormFromContinuous_pairing (F : C(FrameBundle g, FourSpace))
    (u : smoothCovariantFields M 1) :
    inner ℝ (oneFormFromContinuous (o := o) F) (smoothOneFormL2Linear u) =
      ∫ e, inner ℝ (F e) (smoothOneFormEuclideanValue (g := g) u e)
        ∂canonicalFrameMeasure g o := by
  change inner ℝ (oneFormFromFrameL2 (ContinuousMap.toLp 2 (canonicalFrameMeasure g o) ℝ F))
    (smoothOneFormL2Linear u) = _
  rw [oneFormFromFrameL2_pairing, oneFormFrameL2_smooth, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o) F,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (canonicalFrameMeasure g o)
      (smoothOneFormEuclideanValue (g := g) u)] with e hF hu
  rw [hF, hu]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A compact finite-regularity normal-frame amplitude determines an
actual element of the global one-form L2 space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem heatNormalOneAmplitudeL2_pairing (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M) (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : smoothCovariantFields M 1) :
    inner ℝ (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothOneFormL2Linear v) =
      ∫ f, inner ℝ (heatNormalOneAmplitude D C hCt hP hD a ha hc hs f)
        (smoothOneFormEuclideanValue (g := g) v f) ∂canonicalFrameMeasure g o :=
  oneFormFromContinuous_pairing _ v

end
end PositiveEinsteinFour.Geometry
end


section

/-! Pairing compact normal one-form amplitudes with actual smooth sections. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem heatNormalOneLift_pairing (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (v : smoothCovariantFields M 1) (f : FrameBundle g) :
    inner ℝ (WithLp.toLp 2
      (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i]) : FourSpace)
      (smoothOneFormEuclideanValue (g := g) v f) =
    heatNormalScalarLift C (fun x => inner ℝ (a x) (heatNormalOneValue c D.point v x)) f.base := by
  classical
  change inner ℝ (WithLp.toLp 2 (fun i => heatNormalOneFrameLift g c C (heatNormalOneCoordinates D a) f ![i]) : FourSpace)
    (WithLp.toLp 2 (fun i => covariantFieldFramed g v.val f ![i])) = _
  rw [heat_oneTensor_inner]
  by_cases hf : f.base ∈ C.target
  · let x := C.symm f.base
    have hx : x ∈ C.source := C.map_target hf
    have hxb := hD hx
    have hbase : (D.point x).1 = chartAt FourSpace c f.base := by
      rw [D.exponential x hxb, ← hE hx, C.right_inv hf]
    have hF := frameChartMatrix_normalizes g c f (hCt hf)
    rw [← hbase] at hF
    rw [heatNormalOneFrameLift, ite_eq_left hf, heatNormalScalarLift_on_target C _ hf,
      heatNormalOneCoordinates, heat_covariantField_chart g v.val c f (hCt hf)]
    change frameTensorPairing
      (frameTensor (frameChartMatrix g c f) (frameTensor (D.point x).2⁻¹ (fun v => a x (v 0))))
      (frameTensor (frameChartMatrix g c f) (covariantFieldCoordinates v.val c (chartAt FourSpace c f.base))) = _
    rw [← hbase, heat_normal_one_pairing _ _ _ (D.orthonormal x hxb) hF]
    have h := heat_oneTensor_inner (fun q => a x (q 0))
      (frameTensor (D.point x).2 (covariantFieldCoordinates v.val c (D.point x).1))
    exact h.symm
  · rw [heatNormalOneFrameLift, ite_eq_right hf, heatNormalScalarLift, ite_eq_right hf]
    simp only [frameTensorPairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The global L2 amplitude has the expected scalar base integral against
every actual smooth test section. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.heatNormalOneAmplitudePairing_probability
theorem heatNormalOneAmplitudeL2_pairing_base (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : smoothCovariantFields M 1) :
    inner ℝ (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothOneFormL2Linear v) =
      ∫ y, heatNormalScalarLift C
        (fun x => inner ℝ (a x) (heatNormalOneValue c D.point
          v x)) y ∂normalizedVolume g := by
  let ψ := fun x => inner ℝ (a x) (heatNormalOneValue c D.point
    v x)
  have hψs : tsupport ψ ⊆ tsupport a := by
    apply closure_mono
    intro x hx
    contrapose! hx
    have ha0 := Function.notMem_support.mp hx
    apply Function.notMem_support.mpr
    simp only [ψ, ha0, inner_zero_left]
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hψs
  have hψ : ContinuousOn ψ C.source := by
    intro x hx
    have hv : ContDiffAt ℝ 2 (heatNormalOneValue c D.point v) x := by
      apply (contDiffAt_piLp (p := 2)).mpr
      intro k
      exact heatNormalOneFormValue_regular 2 c D.point v x
        (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx)) k
    exact (ha.continuous.continuousAt.inner hv.continuousAt).continuousWithinAt
  have hL := heatNormalScalarLift_continuous C ψ hψ hψc (hψs.trans hs)
  have hLi : Integrable (heatNormalScalarLift C ψ) (normalizedVolume g) :=
    hL.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [heatNormalOneAmplitudeL2_pairing]
  have hp (f : FrameBundle g) :
      inner ℝ (heatNormalOneAmplitude D C hCt hP hD a ha hc hs f)
        (smoothOneFormEuclideanValue (g := g) v f) =
      heatNormalScalarLift C ψ f.base :=
    heatNormalOneLift_pairing D C hE hCt hD a v f
  simp_rw [hp]
  rw [canonicalFrameMeasure_integral_base g o _ hLi]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact normal-coordinate pairings of the actual global L2 amplitude. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

theorem heatNormalOneAmplitudeL2_pairing_normal (D : HeatNormalFrameData g o c e)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (v : smoothCovariantFields M 1) :
    inner ℝ (heatNormalOneAmplitudeL2 D C hCt hP hD a ha hc hs) (smoothOneFormL2Linear v) =
      (normalizedChartFactor g).toReal * ∫ x, frameExponentialJacobian g o e x *
        inner ℝ (a x) (heatNormalOneValue c D.point
          v x) := by
  rw [heatNormalOneAmplitudeL2_pairing_base D C hE]
  apply heatNormalScalarLift_integral D C hE hCt hP hD
  apply subset_trans (closure_mono ?_) hs
  intro x hx
  contrapose! hx
  apply Function.notMem_support.mpr
  rw [Function.notMem_support.mp hx, inner_zero_left]

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

theorem HeatNormalFrameData.potential_symmetric (D : HeatNormalFrameData g o c e)
    (x : FourSpace) (hx : x ∈ ball 0 D.radius) (k l : Fin 6) :
    heatNormalPotential g c D.point x k l = heatNormalPotential g c D.point x l k := by
  have hR : ∀ i j a b, twoFormMetricCurvatureTensor g (D.frame x hx) ![a,b,i,j] =
      twoFormMetricCurvatureTensor g (D.frame x hx) ![i,j,a,b] := by
    intro i j a b
    change frameTensor (D.frame x hx).frame.matrix _ ![a,b,i,j] =
      frameTensor (D.frame x hx).frame.matrix _ ![i,j,a,b]
    rw [frameTensor_curvatureCoordinates, frameTensor_curvatureCoordinates]
    exact frame_algebraic_pairSymmetric (D.frame x hx).frame
      (frame_algebraic_lastSkew (D.frame x hx).frame) i j a b
  have hC := twoFormCurvatureMatrix_symmetric (twoFormMetricCurvatureTensor g (D.frame x hx)) hR
  have hP : (twoFormPotentialMatrix (twoFormMetricCurvatureTensor g (D.frame x hx)))ᵀ =
      twoFormPotentialMatrix (twoFormMetricCurvatureTensor g (D.frame x hx)) := by
    simp only [twoFormPotentialMatrix, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, hC]
  rw [D.potential_as_actual x hx]
  exact (congrArg (fun A : TwoFormMatrix => A k l) hP).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The extended bundle operator is the genuine normal covariant
operator on every compact amplitude supported in its agreement region. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalBundleExtension.compact_operator_eq
    (E : HeatNormalBundleExtension D) (U : Set FourSpace)
    (hU : ∀ x ∈ U, ∀ u : FourSpace → Fin 6 → ℝ,
      (∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) → ∀ k,
      fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x) u x k =
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) u x k)
    (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a)
    (hs : tsupport a ⊆ U) (x : FourSpace) (k : Fin 6) :
    heatNormalOperatorAmplitude E a x k =
      fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x)
        (fun y l => a y l) x k := by
  by_cases hx : x ∈ U
  · exact hU x hx (fun y l => a y l)
      (fun l => ((contDiff_piLp (p := 2)).mp ha l).contDiffAt) k
  · have hz : ∀ l, (fun y => a y l) =ᶠ[𝓝 x] (fun _ => 0) := by
      intro l
      have hn : x ∉ tsupport a := fun h => hx (hs h)
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hn] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy]
      rfl
    change fourHeatBundleOperator _ _ _ _ _ x k = _
    rw [fourHeatBundleOperator_zero_of_locally_zero _ _ _ _ hz,
      fourHeatCovariantOperator_zero_of_locally_zero _ _ _ _ hz]

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

theorem HeatCommonNormalMember.green_regular (N : HeatCommonNormalMember g o c E r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) :
    (∀ i k l, ContDiffAt ℝ 1 (fun y => heatTwoFormConnection g c N.frameData.point i y k l) x) ∧
    (∀ i j, ContDiffAt ℝ 1 (fun y => (heatNormalMetric g o e y)⁻¹ i j) x) ∧
    ContDiffAt ℝ 1 (frameExponentialJacobian g o e) x ∧
    0 < frameExponentialJacobian g o e x ∧
    (∀ k l, ContinuousAt (fun y => heatNormalPotential g c N.frameData.point y k l) x) := by
  have hxD := ball_subset_ball N.radius_le hx
  have hJg : frameExponentialJacobian g o e =ᶠ[𝓝 x]
      (fun y => (N.extension.base.U y ^ 2)⁻¹) := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    have hh := heatNormalLeadingAmplitude_normalization g o e y
      (Real.sqrt_pos.mpr (N.metric_pos y hy))
    rw [← (N.actual y hy).2.2.2.2] at hh
    exact eq_inv_of_mul_eq_one_right hh
  refine ⟨?_, ?_, ?_, Real.sqrt_pos.mpr (N.metric_pos x hx), ?_⟩
  · intro i k l
    exact heatTwoFormConnection_contDiffAt 1 c N.frameData.point x (N.point_regular x hx)
      (N.frameData.in_chart x hxD) (N.frame_det x hx) i k l
  · intro i j
    have hg : (fun y => N.extension.base.a y i j) =ᶠ[𝓝 x]
        (fun y => (heatNormalMetric g o e y)⁻¹ i j) := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact congrArg (fun A : Mat4 => A i j) (N.actual y hy).1
    exact ((N.extension.base.a_regular i j).of_le (by norm_num)).contDiffAt.congr_of_eventuallyEq hg.symm
  · exact (((N.extension.base.U_regular.of_le (show (1 : ℕ∞ω) ≤ 10 by norm_num)).contDiffAt.pow 2).inv
      (pow_ne_zero 2 (N.extension.base.U_pos x).ne')).congr_of_eventuallyEq hJg
  · intro k l
    exact (heatNormalPotential_contDiffAt 2 g c N.frameData.point x (N.point_regular x hx)
      (N.frameData.in_chart x hxD) k l).continuousAt

theorem HeatCommonNormalMember.connection_operator (N : HeatCommonNormalMember g o c E r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) (u : FourSpace → Fin 6 → ℝ)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (k : Fin 6) :
    fourHeatBundleOperator (N.extension.base.a x) (N.extension.base.b x)
      (N.extension.B x) (N.extension.C x) u x k =
    fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatTwoFormConnection g c N.frameData.point) (heatNormalPotential g c N.frameData.point x) u x k := by
  obtain ⟨ha, hb, hB, hC, _⟩ := N.actual x hx
  rw [ha, hb, hB, hC]
  exact (heatNormalConnectionOperator_eq N.frameData u x
    (fun i k l => ((N.green_regular x hx).1 i k l).differentiableAt one_ne_zero) hu k).symm

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatCommonNormalMember.actual_bundle_operator (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (x : FourSpace) (hx : x ∈ ball 0 r) (u : smoothTwoForms o) (k : Fin 6) :
    fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatNormalBundleFirst N.frameData x) (heatNormalBundleZero N.frameData x)
      (fun y l => heatNormalTwoFormValue o c N.frameData.point u.val y l) x k =
    heatNormalTwoFormValue o c N.frameData.point (smoothHodgeLaplacian hRic u).val x k :=
  N.frameData.actual_bundle_operator_at hRic x (ball_subset_ball N.radius_le hx)
    (N.point_regular x hx) (N.exponential_source x hx) (N.metric_pos x hx) u k

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual compact one-form amplitudes satisfy the geometric Green identity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalOneExtension.compact_operator_eq
    (E : HeatNormalOneExtension D) (U : Set FourSpace)
    (hU : ∀ x ∈ U, ∀ u : FourSpace → Fin 4 → ℝ,
      (∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) → ∀ k,
      fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x) u x k =
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4))) u x k)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a)
    (hs : tsupport a ⊆ U) (x : FourSpace) (k : Fin 4) :
    heatNormalOneOperatorAmplitude E a x k =
      fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalFrameConnection g c D.point) (((3 : ℝ) • (1 : Mat4)))
        (fun y l => a y l) x k := by
  by_cases hx : x ∈ U
  · exact hU x hx (fun y l => a y l)
      (fun l => ((contDiff_piLp (p := 2)).mp ha l).contDiffAt) k
  · have hz : ∀ l, (fun y => a y l) =ᶠ[𝓝 x] (fun _ => 0) := by
      intro l
      have hn : x ∉ tsupport a := fun h => hx (hs h)
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hn] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy]
      rfl
    change fourHeatOneOperator _ _ _ _ _ x k = _
    rw [fourHeatOneOperator_zero_of_locally_zero _ _ _ _ hz,
      fourHeatOneCovariantOperator_zero_of_locally_zero _ _ _ _ hz]


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

def heatNormalOneHodgeImage (E : HeatNormalOneExtension D)
    (C : OpenPartialHomeomorph FourSpace M)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) : OneFormL2 o :=
  heatNormalOneAmplitudeL2 D C hCt hP hD (heatNormalOneOperatorAmplitude E a)
    (heatNormalOneOperatorAmplitude_regular E a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneOperatorAmplitude_support E a))
    ((heatNormalOneOperatorAmplitude_support E a).trans hs)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Green's identity throughout the common normal ball, with the actual
operator and no additional small-support neighborhood. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {E : HeatFamilySmoothCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonNormalMember.compact_green (N : HeatCommonNormalMember g o c E r e)
    (hRic : RicciThree g) (a : FourSpace → TwoFormFour) (ha : ContDiff ℝ 2 a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ ball 0 r) (v : smoothTwoForms o) :
    (∫ x, frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalTwoFormValue o c N.frameData.point (smoothHodgeLaplacian hRic v).val x)) =
    ∫ x, frameExponentialJacobian g o e x *
      inner ℝ (heatNormalOperatorAmplitude N.extension a x)
        (heatNormalTwoFormValue o c N.frameData.point v.val x) := by
  let u := fun x k => a x k
  let w := fun x k => heatNormalTwoFormValue o c N.frameData.point v.val x k
  have hu (k : Fin 6) : ContDiff ℝ 2 (fun x => u x k) :=
    (contDiff_piLp (p := 2)).mp ha k
  have hsc (k : Fin 6) : tsupport (fun x => u x k) ⊆ ball 0 r :=
    (heatAmplitude_component_support a k).trans hs
  have hcc (k : Fin 6) : HasCompactSupport (fun x => u x k) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (heatAmplitude_component_support a k)
  have hw (x : FourSpace) (hx : x ∈ ball 0 r) (k : Fin 6) :
      ContDiffAt ℝ 2 (fun y => w y k) x := by
    have h := heatNormalTwoFormValue_contDiffAt 2 v.property c N.frameData.point x
      (N.point_regular x hx) (N.frameData.in_chart x (ball_subset_ball N.radius_le hx))
    exact (contDiffAt_piLp (p := 2)).mp h k
  have hop (x : FourSpace) (k : Fin 6) : heatNormalOperatorAmplitude N.extension a x k =
      fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatTwoFormConnection g c N.frameData.point) (heatNormalPotential g c N.frameData.point x) u x k :=
    N.extension.compact_operator_eq (ball 0 r) (fun y hy => N.connection_operator y hy) a ha hs x k
  have htest (x : FourSpace) : frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalTwoFormValue o c N.frameData.point (smoothHodgeLaplacian hRic v).val x) =
      ∑ k : Fin 6, frameExponentialJacobian g o e x * u x k *
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c N.frameData.point) (heatNormalPotential g c N.frameData.point x) w x k := by
    rw [heat_weighted_inner_sum]
    by_cases hx : x ∈ ball 0 r
    · apply Finset.sum_congr rfl
      intro k _
      have hactual := N.actual_bundle_operator hRic x hx v k
      have hconv := heatNormalConnectionOperator_eq N.frameData w x
        (fun i k l => ((N.green_regular x hx).1 i k l).differentiableAt one_ne_zero) (hw x hx) k
      rw [← hconv] at hactual
      rw [hactual]
    · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      have hzk (k : Fin 6) : u x k = 0 := by change a x k = 0; rw [hz]; rfl
      simp only [hz, PiLp.zero_apply, hzk, mul_zero, zero_mul, Finset.sum_const_zero]
  have hg := fourHeatCovariantOperator_compact_adjoint
    (heatTwoFormConnection g c N.frameData.point) (fun x => (heatNormalMetric g o e x)⁻¹)
    (frameExponentialJacobian g o e) (heatNormalPotential g c N.frameData.point) u w (ball 0 r)
    hu hcc hsc hw (fun x hx => (N.green_regular x hx).1) (fun x hx => (N.green_regular x hx).2.1)
    (fun x hx => (N.green_regular x hx).2.2.1) (fun x hx => (N.green_regular x hx).2.2.2.1.ne')
    (fun x hx => (N.green_regular x hx).2.2.2.2)
    (fun _ _ i => heatTwoFormConnectionMatrix_skew _)
    (fun x _ i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun x hx => N.frameData.potential_symmetric x (ball_subset_ball N.radius_le hx))
  calc
    _ = ∫ x, ∑ k : Fin 6, frameExponentialJacobian g o e x * u x k *
        fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatTwoFormConnection g c N.frameData.point) (heatNormalPotential g c N.frameData.point x) w x k := by
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

def HeatNormalParametrixData.oneOperatorColumn (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (t : ℝ) (l : Fin 4) : OneFormL2 o :=
  heatNormalOneHodgeImage E P.chart P.in_chart P.point_regular P.inside_radius
    (heatNormalOneCutoffColumn E P.cutoff t l)
    (heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support E P.cutoff t l))
    ((heatNormalOneCutoffColumn_support E P.cutoff t l).trans P.cutoff_support)

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

/-! Exact one-form transport and residual on the entire common normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.one_transport (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r) :
    (∀ i, ∑ j : Fin 4, N.one.base.a x i j * x j = x i) ∧
    (∀ j, ∑ i : Fin 4, N.one.base.a x i j * x i = x j) ∧
    fourHeatEikonalDefect (N.one.base.a x) x = 0 ∧
    fourHeatRadialTransport (N.one.base.a x) (N.one.base.b x) N.one.base.U x = 0 ∧
    (∀ k l, (∑ i : Fin 4, x i * N.one.B x i k l) = 0) := by
  rw [N.one_base]
  obtain ⟨hrow, hcol, heik, hU, _⟩ := N.normal.transport hRic he x hx
  refine ⟨hrow, hcol, heik, hU, ?_⟩
  intro k l
  rw [(N.one_actual x hx).1]
  have h := N.normal.frameData.oneFirst_radial hRic he x
    (ball_subset_ball N.normal.radius_le hx) (N.normal.metric_pos x hx).ne'
  simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    using congrArg (fun B : Mat4 => B k l) h

theorem HeatCommonEulerMember.one_amplitude_transport (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (m : ℕ) (hm : m ≤ 2) (k l : Fin 4) :
    fourHeatRadialTransport (N.one.base.a x) (N.one.base.b x)
      (fun y => N.one.amplitude (m + 1) y k l) x +
      (m + 1 : ℝ) * N.one.amplitude (m + 1) x k l =
    -fourHeatOneOperator (N.one.base.a x) (N.one.base.b x)
      (N.one.B x) (N.one.C x) (fun y q => N.one.amplitude m y q l) x k := by
  obtain ⟨hrow, hcol, _, hU, _⟩ := N.one_transport hRic he x hx
  exact fourHeatOneCoefficient_transport m _ _ _ _ _ x
    (N.one.base.U_regular.of_le (by norm_num)) (fun y => (N.one.base.U_pos y).ne')
    (fun i j => (N.one.base.a_regular i j).of_le (by norm_num))
    (fun i => (N.one.base.b_regular i).of_le (by norm_num))
    (fun i k l => (N.one.B_regular i k l).of_le (by norm_num))
    (fun k l => (N.one.C_regular k l).of_le (by norm_num))
    (fun k l => (N.one.amplitude_regular m (by omega) k l).of_le (by norm_num))
    hrow hcol hU k l

theorem HeatCommonEulerMember.one_parametrix_residual (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (t : ℝ) (ht : 0 < t) (k l : Fin 4) :
    deriv (fun s => heatNormalOneParametrix N.one s x k l) t +
      fourHeatOneOperator (N.one.base.a x) (N.one.base.b x)
        (N.one.B x) (N.one.C x)
        (fun y q => heatNormalOneParametrix N.one t y q l) x k =
    fourHeatGaussian t x * t ^ 3 * F.lastCoefficient (x, frameCoordinateState g c e) k l := by
  obtain ⟨_, _, hEik, hU, hrad⟩ := N.one_transport hRic he x hx
  have hreg (m : Fin 4) (q : Fin 4) : ContDiff ℝ 2 (fun y => N.one.amplitude m y q l) :=
    (N.one.amplitude_regular m (by omega) q l).of_le (by norm_num)
  have hzero (q : Fin 4) : fourHeatRadialTransport (N.one.base.a x) (N.one.base.b x)
      (fun y => N.one.amplitude 0 y q l) x = 0 := by
    by_cases hql : q = l
    · subst q
      simpa [HeatNormalOneExtension.amplitude, fourHeatOneCoefficient] using hU
    · have hz : (fun y => N.one.amplitude 0 y q l) = fun _ => (0 : ℝ) := by
        funext y
        simp [HeatNormalOneExtension.amplitude, fourHeatOneCoefficient, hql]
      rw [hz]
      simpa only [zero_mul] using
        fourHeatRadialTransport_const_mul (N.one.base.a x) (N.one.base.b x) 0 N.one.base.U x
  have hh := fourHeatOnePolynomial_gaussian_residual (N.one.base.a x) (N.one.base.b x)
    (N.one.B x) (N.one.C x) (fun m y q => N.one.amplitude m y q l) hreg t ht x hrad hEik hzero
    (by intro q; simpa using N.one_amplitude_transport hRic he x hx 0 (by omega) q l)
    (by intro q; convert N.one_amplitude_transport hRic he x hx 1 (by omega) q l using 1 <;> norm_num)
    (by intro q; convert N.one_amplitude_transport hRic he x hx 2 (by omega) q l using 1 <;> norm_num) k
  refine hh.trans ?_
  congr 1
  change fourHeatOneOperator (N.one.base.a x) (N.one.base.b x)
    (N.one.B x) (N.one.C x) (fun y q => N.one.amplitude 3 y q l) x k = _
  rw [show N.one.amplitude 3 = fun y => F.amplitude 3 (y, frameCoordinateState g c e)
    from N.one_amplitude_family 3 (by omega)]
  rw [N.one_base, N.normal.a_family, N.normal.b_family, N.one_B_family, N.one_C_family]
  exact (heatFamilyOneOperator_slice F.base.a F.base.b F.B F.C _
    (fun q => (F.amplitude_regular 3 (by omega) q l).of_le (by norm_num)) _ k).symm


end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form operator and Green coefficients on the common normal ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.one_green_regular (N : HeatCommonEulerMember g o c F r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) :
    (∀ i k l, ContDiffAt ℝ 1 (fun y => heatNormalFrameConnection g c N.normal.frameData.point i y k l) x) ∧
    (∀ i j, ContDiffAt ℝ 1 (fun y => (heatNormalMetric g o e y)⁻¹ i j) x) ∧
    ContDiffAt ℝ 1 (frameExponentialJacobian g o e) x ∧
    0 < frameExponentialJacobian g o e x := by
  refine ⟨?_, (N.normal.green_regular x hx).2.1, (N.normal.green_regular x hx).2.2.1,
    (N.normal.green_regular x hx).2.2.2.1⟩
  intro i k l
  exact heatNormalFrameConnection_contDiffAt 1 g c N.normal.frameData.point x
    (N.normal.point_regular x hx)
    (N.normal.frameData.in_chart x (ball_subset_ball N.normal.radius_le hx))
    (N.normal.frame_det x hx) i k l

theorem HeatCommonEulerMember.one_connection_operator (N : HeatCommonEulerMember g o c F r e)
    (x : FourSpace) (hx : x ∈ ball 0 r) (u : FourSpace → Fin 4 → ℝ)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (k : Fin 4) :
    fourHeatOneOperator (N.one.base.a x) (N.one.base.b x) (N.one.B x) (N.one.C x) u x k =
    fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatNormalFrameConnection g c N.normal.frameData.point) ((3 : ℝ) • (1 : Mat4)) u x k := by
  rw [N.one_base, (N.normal.actual x hx).1, (N.normal.actual x hx).2.1,
    (N.one_actual x hx).1, (N.one_actual x hx).2]
  unfold heatNormalOneFirst heatNormalOneZero
  exact (fourHeatOneCovariantOperator_eq _ _ _ _ _ x
    (fun i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun i k l => ((N.one_green_regular x hx).1 i k l).differentiableAt one_ne_zero) hu k).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The one-form Green identity holds on the full common chart. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.one_compact_green (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (a : FourSpace → FourSpace) (ha : ContDiff ℝ 2 a)
    (hc : HasCompactSupport a) (hs : tsupport a ⊆ ball 0 r) (v : smoothCovariantFields M 1) :
    (∫ x, frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalOneValue c N.normal.frameData.point (smoothOneFormHodgeLaplacian (o := o) v) x)) =
    ∫ x, frameExponentialJacobian g o e x *
      inner ℝ (heatNormalOneOperatorAmplitude N.one a x) (heatNormalOneValue c N.normal.frameData.point v x) := by
  let u := fun x k => a x k
  let w := fun x k => heatNormalOneFormValue c N.normal.frameData.point v x k
  have hu (k : Fin 4) : ContDiff ℝ 2 (fun x => u x k) :=
    (contDiff_piLp (p := 2)).mp ha k
  have hsc (k : Fin 4) : tsupport (fun x => u x k) ⊆ ball 0 r :=
    (heatOneAmplitude_component_support a k).trans hs
  have hcc (k : Fin 4) : HasCompactSupport (fun x => u x k) :=
    hc.of_isClosed_subset (isClosed_tsupport _) (heatOneAmplitude_component_support a k)
  have hw (x : FourSpace) (hx : x ∈ ball 0 r) (k : Fin 4) :
      ContDiffAt ℝ 2 (fun y => w y k) x := by
    exact heatNormalOneFormValue_regular 2 c N.normal.frameData.point v x
      (N.normal.point_regular x hx) (N.normal.frameData.in_chart x (ball_subset_ball N.normal.radius_le hx)) k
  have hop (x : FourSpace) (k : Fin 4) : heatNormalOneOperatorAmplitude N.one a x k =
      fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalFrameConnection g c N.normal.frameData.point) (((3 : ℝ) • (1 : Mat4))) u x k :=
    N.one.compact_operator_eq (ball 0 r) (fun y hy => N.one_connection_operator y hy) a ha hs x k
  have htest (x : FourSpace) : frameExponentialJacobian g o e x *
      inner ℝ (a x) (heatNormalOneValue c N.normal.frameData.point (smoothOneFormHodgeLaplacian (o := o) v) x) =
      ∑ k : Fin 4, frameExponentialJacobian g o e x * u x k *
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c N.normal.frameData.point) (((3 : ℝ) • (1 : Mat4))) w x k := by
    rw [heat_one_weighted_inner_sum]
    by_cases hx : x ∈ ball 0 r
    · apply Finset.sum_congr rfl
      intro k _
      have hactual := N.actual_one_operator hRic x hx v k
      have hconv := fourHeatOneCovariantOperator_eq
        (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
        (heatNormalFrameConnection g c N.normal.frameData.point) ((3 : ℝ) • (1 : Mat4)) w x
        (fun i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
        (fun i k l => ((N.one_green_regular x hx).1 i k l).differentiableAt one_ne_zero) (hw x hx) k
      unfold heatNormalOneFirst heatNormalOneZero at hactual
      rw [← hconv] at hactual
      rw [hactual]
      rfl
    · have hz : a x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      have hzk (k : Fin 4) : u x k = 0 := by change a x k = 0; rw [hz]; rfl
      simp only [hz, PiLp.zero_apply, hzk, mul_zero, zero_mul, Finset.sum_const_zero]
  have hg := fourHeatOneCovariantOperator_compact_adjoint
    (heatNormalFrameConnection g c N.normal.frameData.point) (fun x => (heatNormalMetric g o e x)⁻¹)
    (frameExponentialJacobian g o e) ((fun _ : FourSpace => (3 : ℝ) • (1 : Mat4))) u w (ball 0 r)
    hu hcc hsc hw (fun x hx => (N.one_green_regular x hx).1) (fun x hx => (N.one_green_regular x hx).2.1)
    (fun x hx => (N.one_green_regular x hx).2.2.1) (fun x hx => (N.one_green_regular x hx).2.2.2.ne')
    (fun _ _ _ _ => continuousAt_const)
    (fun x hx i => N.normal.frameData.connection_skew x (ball_subset_ball N.normal.radius_le hx) i)
    (fun x _ i j => (congrArg (fun A : Mat4 => A i j) (heatNormalInverse_symm g o e x)).symm)
    (fun _ _ k l => by simp [Matrix.one_apply, eq_comm])
  calc
    _ = ∫ x, ∑ k : Fin 4, frameExponentialJacobian g o e x * u x k *
        fourHeatOneCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
          (heatNormalFrameConnection g c N.normal.frameData.point) (((3 : ℝ) • (1 : Mat4))) w x k := by
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

/-! Scalar and one-form data on the same actual chart and fixed cutoff as degree two. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.scalarData_actual (N : HeatCommonEulerMember g o c F r e)
    (hr : 0 < r) :
    (∀ x ∈ tsupport (N.scalarData hr).cutoff,
      (N.scalarData hr).extension.a x = (heatNormalMetric g o e x)⁻¹) ∧
    (∀ x ∈ tsupport (N.scalarData hr).cutoff,
      (N.scalarData hr).extension.b x = heatNormalDrift g o e x) ∧
    (∀ x ∈ tsupport (N.scalarData hr).cutoff, 0 < (heatNormalMetric g o e x).det) := by
  have hs : tsupport (N.scalarData hr).cutoff ⊆ Metric.ball 0 r := by
    exact (N.scalarData hr).cutoff_support.trans (by
      rw [show (N.scalarData hr).chart = (N.normal.parametrixData hr).chart from rfl,
        N.normal.parametrixData_source hr])
  exact ⟨fun x hx => (N.normal.actual x (hs hx)).1,
    fun x hx => (N.normal.actual x (hs hx)).2.1,
    fun x hx => N.normal.metric_pos x (hs hx)⟩

variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]

theorem HeatCommonEulerMember.one_compact_operator_pairing
    (N : HeatCommonEulerMember g o c F r e) (hRic : RicciThree g)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 N.normal.frameData.point C.source)
    (hD : C.source ⊆ Metric.ball 0 N.normal.frameData.radius)
    (a : FourSpace → FourSpace) (ha : ContDiff ℝ 4 a) (hc : HasCompactSupport a)
    (hs : tsupport a ⊆ C.source) (hsmall : tsupport a ⊆ Metric.ball 0 r)
    (v : smoothCovariantFields M 1) :
    inner ℝ (heatNormalOneAmplitudeL2 N.normal.frameData C hCt hP hD a
      (ha.of_le (by norm_num)) hc hs)
      (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
    inner ℝ (heatNormalOneHodgeImage N.one C hCt hP hD a ha hc hs)
      (smoothOneFormL2Linear v) := by
  have hleft := heatNormalOneAmplitudeL2_pairing_normal N.normal.frameData C hE hCt hP hD a
    (ha.of_le (by norm_num)) hc hs (smoothOneFormHodgeLaplacian (o := o) v)
  have hright := heatNormalOneAmplitudeL2_pairing_normal N.normal.frameData C hE hCt hP hD
    (heatNormalOneOperatorAmplitude N.one a) (heatNormalOneOperatorAmplitude_regular N.one a ha)
    (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneOperatorAmplitude_support N.one a))
    ((heatNormalOneOperatorAmplitude_support N.one a).trans hs) v
  exact hleft.trans ((congrArg ((normalizedChartFactor g).toReal * ·)
    (N.one_compact_green hRic a (ha.of_le (by norm_num)) hc hsmall v)).trans hright.symm)

theorem HeatCommonEulerMember.parametrixData_one_pairing
    (N : HeatCommonEulerMember g o c F r e) (hr : 0 < r) (hRic : RicciThree g)
    (t : ℝ) (l : Fin 4) (v : smoothCovariantFields M 1) :
    inner ℝ ((N.normal.parametrixData hr).oneColumn N.one t l)
      (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
    inner ℝ ((N.normal.parametrixData hr).oneOperatorColumn N.one t l)
      (smoothOneFormL2Linear v) := by
  let P := N.normal.parametrixData hr
  apply N.one_compact_operator_pairing hRic P.chart P.exponential P.in_chart P.point_regular
    P.inside_radius (heatNormalOneCutoffColumn N.one P.cutoff t l)
    (heatNormalOneCutoffColumn_regular N.one P.cutoff P.cutoff_regular t l)
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support N.one P.cutoff t l))
    ((heatNormalOneCutoffColumn_support N.one P.cutoff t l).trans P.cutoff_support) _ v
  rw [← N.normal.parametrixData_source hr]
  exact (heatNormalOneCutoffColumn_support N.one P.cutoff t l).trans P.cutoff_support

end
end PositiveEinsteinFour.Geometry
end


section

/-! The scalar transport residual is the common last coefficient throughout the ball. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter Metric
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M}
  {F : HeatFamilyOneCoefficients} {r : ℝ} {e : FrameBundle g}

theorem HeatCommonEulerMember.scalar_amplitude_transport (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (m : ℕ) (hm : m ≤ 2) :
    fourHeatRadialTransport (N.normal.extension.base.a x) (N.normal.extension.base.b x)
      (N.normal.extension.base.scalarAmplitude (m + 1)) x +
      (m + 1 : ℝ) * N.normal.extension.base.scalarAmplitude (m + 1) x =
    -fourHeatLocalOperator (N.normal.extension.base.a x) (N.normal.extension.base.b x) 0
      (N.normal.extension.base.scalarAmplitude m) x := by
  obtain ⟨hrow, hcol, _, hU, _⟩ := N.normal.transport hRic he x hx
  let A := N.normal.extension.base
  exact fourHeatCoefficient_transport m A.a A.b (fun _ => 0) A.U x
    (A.U_regular.of_le (by norm_num)) (fun y => (A.U_pos y).ne')
    (fun i j => (A.a_regular i j).of_le (by norm_num))
    (fun i => (A.b_regular i).of_le (by norm_num)) contDiff_const
    ((A.scalarAmplitude_regular m (by omega)).of_le (by norm_num)) hrow hcol hU

theorem HeatCommonEulerMember.scalar_parametrix_residual (N : HeatCommonEulerMember g o c F r e)
    (hRic : RicciThree g) (he : e ∈ o.positive) (x : FourSpace) (hx : x ∈ ball 0 r)
    (t : ℝ) (ht : 0 < t) :
    deriv (fun s => N.normal.extension.base.scalarParametrix s x) t +
      fourHeatLocalOperator (N.normal.extension.base.a x) (N.normal.extension.base.b x) 0
        (N.normal.extension.base.scalarParametrix t) x =
    fourHeatGaussian t x * t ^ 3 * F.base.scalarLastCoefficient (x, frameCoordinateState g c e) := by
  obtain ⟨_, _, heik, hU, _⟩ := N.normal.transport hRic he x hx
  let A := N.normal.extension.base
  have h := fourHeatPolynomial_gaussian_residual (A.a x) (A.b x) 0
    (fun m : Fin 4 => A.scalarAmplitude m)
    (fun m => (A.scalarAmplitude_regular m (by omega)).of_le (by norm_num)) t ht x heik hU
    (by simpa using N.scalar_amplitude_transport hRic he x hx 0 (by omega))
    (by convert N.scalar_amplitude_transport hRic he x hx 1 (by omega) using 1 <;> norm_num [A])
    (by convert N.scalar_amplitude_transport hRic he x hx 2 (by omega) using 1 <;> norm_num [A])
  refine h.trans ?_
  congr 1
  change fourHeatLocalOperator (N.normal.extension.base.a x) (N.normal.extension.base.b x) 0
    (N.normal.extension.base.scalarAmplitude 3) x = _
  rw [N.scalar_amplitude_family 3 (by omega), N.normal.a_family, N.normal.b_family]
  exact (heatFamilyScalarOperator_slice F.base.a F.base.b _
    ((F.base.scalarAmplitude_regular 3 (by omega)).of_le (by norm_num)) _).symm

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


