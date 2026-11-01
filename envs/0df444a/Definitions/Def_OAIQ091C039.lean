-- Prove2me | Definitions.Def_OAIQ091C039
-- name    : OAIQ091C039
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T17:56:38.496537+00:00
-- url     : https://prove2.me/theorems/948e5146-0d4c-4315-af5b-1f2f7d6060f8
-- title:
--   Definitions bundle OAIQ091C039 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 138 declarations of OpenAI's Lean: 23 definitions and 115 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.densityCutoffL2`, `OAI.PositiveEinsteinFour.Geometry.fourHeatOneCovariantFlux`, `OAI.PositiveEinsteinFour.Geometry.frameFullInitialVariation`, `OAI.PositiveEinsteinFour.Geometry.frozenScalarPrincipal`, `OAI.PositiveEinsteinFour.Geometry.heatMatrixScalarOperator`, `OAI.PositiveEinsteinFour.Geometry.heatNormalMatrixPolynomial`, `OAI.PositiveEinsteinFour.Geometry.heatNormalOneOperatorAmplitude`, `OAI.PositiveEinsteinFour.Geometry.heatNormalOneValue`, `OAI.PositiveEinsteinFour.Geometry.heatNormalOperatorAmplitude`, `OAI.PositiveEinsteinFour.Geometry.heatNormalTwoFormNabla`, `OAI.PositiveEinsteinFour.Geometry.heatNormalTwoFormValue`, `OAI.PositiveEinsteinFour.Geometry.heatOneMatrixScalarOperator`, `OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFourSpace`, `OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFourSpace_2`, `OAI.PositiveEinsteinFour.Geometry.instMeasureSpaceFourSpace`, `OAI.PositiveEinsteinFour.Geometry.instMeasureSpaceFourSpace_2`, `OAI.PositiveEinsteinFour.Geometry.radialVariationInFrame`, `OAI.PositiveEinsteinFour.Geometry.scalarAffineDistribution`, `OAI.PositiveEinsteinFour.Geometry.scalarAffineJacobian`, `OAI.PositiveEinsteinFour.Geometry.scalarAffineMap`, `OAI.PositiveEinsteinFour.Geometry.scalarAffinePullbackL2`, `OAI.PositiveEinsteinFour.Geometry.scalarAffineTestCLM`, `OAI.PositiveEinsteinFour.Geometry.scalarComplexAffinePullbackL2`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundle `OAIQ091C020` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C026`, `OAIQ091C040`, `OAIQ091C058`, `OAIQ091C060`, `OAIQ091C061`, `OAIQ091C062`, `OAIQ091C063`, `OAIQ091C064`, `OAIQ091C065`, `OAIQ091C067`, `OAIQ091C068`, `OAIQ091C069`, `OAIQ091C070` and `OAIQ091C071`; the statements `OAI_PositiveEinsteinFour_Geometry_FrameReflectionData_opposite_kappaTest_integrable`, `OAI_PositiveEinsteinFour_Geometry_MetricGreenData_kappaTest`, `OAI_PositiveEinsteinFour_HighestHessian_general_plus_energy`, `OAI_PositiveEinsteinFour_HighestHessian_totalMinus_condition` and `OAI_PositiveEinsteinFour_HighestHessian_totalPlus_condition`; the proofs of `OAI_PositiveEinsteinFour_HighestHessian_general_plus_energy` and `OAI_PositiveEinsteinFour_HighestHessian_totalMinus_condition`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C020

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Local ellipticity of the actual scalar operator after freezing an
orthonormal frame at the chart center. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped Manifold ContDiff BigOperators _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

def frozenScalarPrincipal (g : SmoothMetric M) (c : M) (z₀ : ChartTarget c)
    (z : FourSpace) : Mat4 := (frozenFrameMetric g c z₀ z)⁻¹

theorem frozenScalarPrincipal_self (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) : frozenScalarPrincipal g c z₀ z₀ = 1 := by
  rw [frozenScalarPrincipal, frozenFrameMetric_self, inv_one]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal curvature matrix in any fixed chart. This transports the
actual curvature tensor; it does not require a diagonal or moving chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameChart_curvatureEndomorphism (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source) (i j : Fin 4) :
    (frameChartMatrix g c e)⁻¹ *
      pulledCurvatureEndomorphism (frameChartMatrix g c e)
        (fun p q => coordinateCurvatureMatrix g c p q (chartAt FourSpace c e.base))
        i j * frameChartMatrix g c e =
      curvatureEndomorphism (frameCurvature g e.base e.frame) i j := by
  rw [normalized_frame_inverse _ _ (frameChartMatrix_normalizes g c e he)]
  ext a b
  rw [← framed_lowered_endomorphism]
  have hl : loweredMatrixTensor (metricInChart g c (chartAt FourSpace c e.base))
      (fun p q => coordinateCurvatureMatrix g c p q (chartAt FourSpace c e.base)) =
      curvatureCoordinates g c (chartAt FourSpace c e.base) := by
    funext v
    simp only [loweredMatrixTensor, Matrix.mul_apply, coordinateCurvatureMatrix_apply,
      curvatureCoordinates]
    apply Finset.sum_congr rfl
    intro r _
    rw [show metricInChart g c (chartAt FourSpace c e.base) (v 3) r =
      metricInChart g c (chartAt FourSpace c e.base) r (v 3) from g.symm _ _ _]
  rw [hl]
  have ht := congrFun (framedTensor_eq_fixedChart g
    (fun d => curvatureCoordinates g d) (curvatureCoordinates_transition g) c e he)
    ![i,j,b,a]
  rw [frameTensor_curvatureCoordinates] at ht
  exact ht.symm

/-- The curvature action on an arbitrary variation vector has zero
tangential component and the actual normal Jacobi matrix as its tail. -/
theorem frameChart_normal_jacobi_curvature (g : SmoothMetric M) (c : M)
    (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (v : JacobiCoordinateVector) :
    (frameChartMatrix g c e)⁻¹ *ᵥ (jacobiCurvatureCombination
      (fun i j => coordinateCurvatureMatrix g c i j (chartAt FourSpace c e.base))
      (frameChartMatrix g c e *ᵥ v) (fun a => frameChartMatrix g c e a 0) *ᵥ
        (fun a => frameChartMatrix g c e a 0)) =
      Fin.cons 0 ((1 + frameCurvatureField g e) *ᵥ (fun i => v i.succ)) := by
  let w : Fin 4 → ℝ := Fin.cons 0 (fun i => v i.succ)
  have hzero : curvatureEndomorphism (frameCurvature g e.base e.frame) 0 0 = 0 := by
    ext a b
    have h := frameCurvature_first_skew e.frame 0 0 b a
    change frameCurvature g e.base e.frame 0 0 b a = 0
    linarith
  have hsum : (∑ i, v i • curvatureEndomorphism (frameCurvature g e.base e.frame) i 0) =
      ∑ i, w i • curvatureEndomorphism (frameCurvature g e.base e.frame) i 0 := by
    rw [Fin.sum_univ_succ (fun i : Fin 4 => v i •
      curvatureEndomorphism (frameCurvature g e.base e.frame) i 0),
      Fin.sum_univ_succ (fun i : Fin 4 => w i •
        curvatureEndomorphism (frameCurvature g e.base e.frame) i 0)]
    simp only [hzero, smul_zero, zero_add, w, Fin.cons_succ]
  have hmat := jacobiCurvatureCombination_frame (frameChartMatrix g c e)
    (fun i j => coordinateCurvatureMatrix g c i j (chartAt FourSpace c e.base)) v
  simp only [frameChart_curvatureEndomorphism g c e he] at hmat
  rw [hsum] at hmat
  have hcenter := actual_jacobiCurvatureCombination_frame e.frame w
  rw [← hcenter] at hmat
  have h := congrArg (fun A : Mat4 => A *ᵥ Pi.single 0 1) hmat
  have hcol (E : Mat4) : E *ᵥ Pi.single 0 1 = (fun a => E a 0) := by
    ext a
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have haction (A C E : Mat4) : (A * C * E) *ᵥ Pi.single 0 1 =
      A *ᵥ (C *ᵥ (fun a => E a 0)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcol]
  rw [haction, haction] at h
  rw [h]
  exact actual_normal_jacobi_curvature e.frame (fun i => v i.succ)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smoothness of the actual principal coefficients in frozen orthonormal
coordinates.  Only the fixed frame matrix is inverted in this formula. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frozenScalarPrincipal_eq_conjugate (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (z : FourSpace) :
    frozenScalarPrincipal g c z₀ z =
      (chartGramMatrix g c 1 z₀)⁻¹ * (metricInChart g c z)⁻¹ *
        ((chartGramMatrix g c 1 z₀)⁻¹)ᵀ := by
  simp only [frozenScalarPrincipal, frozenFrameMetric, Matrix.mul_inv_rev,
    ← Matrix.transpose_nonsing_inv, Matrix.mul_assoc]

theorem frozenScalarPrincipal_contDiffAt (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target)
    (i j : Fin 4) :
    ContDiffAt ℝ ∞ (fun w => frozenScalarPrincipal g c z₀ w i j) z := by
  simp_rw [frozenScalarPrincipal_eq_conjugate, Matrix.mul_apply]
  apply ContDiffAt.sum
  intro k _
  apply ContDiffAt.mul _ contDiffAt_const
  apply ContDiffAt.sum
  intro l _
  exact contDiffAt_const.mul (scalarPrincipalCoefficients_smooth g c z hz l k)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The derivative of the actual complete radial flow solves the kinetic
variational equation. The proof uses local flow composition at each time. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

/-- A local kinetic flow at the endpoint factors the complete coordinate
flow on a neighborhood of its initial state. -/
theorem radialCoordinateFlow_local_factor (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (p : PositiveRadius × UnitTangentBundle g) (t : ℝ)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d).source) :
    ∃ F : KineticLocalFlow g d (unitRadialCotangentState g d (unitTangentRadialFlow g o t p)),
      ∀ s ∈ Ioo (-F.time) F.time,
        radialCoordinateFlow g o c d (s + t) =ᶠ[𝓝 (unitRadialCotangentState g c p)]
          (fun z => F.map (radialCoordinateFlow g o c d t z, s)) := by
  obtain ⟨U, hU, hpU, F, _hball, hconj⟩ :=
    exists_unitTangent_localHamiltonian g o d (unitTangentRadialFlow g o t p) hd
  refine ⟨F, fun s hs => ?_⟩
  have hr := cotangentRadialRetraction_continuousAt g c (unitRadialCotangentState g c p)
    ⟨(chartAt FourSpace c).map_source hc,
      unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have hf := (unitTangentRadialFlow_continuous g o t).continuousAt.comp hr
  have hpU' : unitTangentRadialFlow g o t
      (cotangentRadialRetraction g c (unitRadialCotangentState g c p)) ∈ U := by
    simpa only [cotangentRadialRetraction_state g c p hc] using hpU
  filter_upwards [hf.preimage_mem_nhds (hU.mem_nhds hpU')] with z hz
  have h := hconj (unitTangentRadialFlow g o t (cotangentRadialRetraction g c z)) hz hs
  change unitRadialCotangentState g d
      (unitTangentRadialFlow g o (s + t) (cotangentRadialRetraction g c z)) = _
  rw [unitTangentRadialFlow_add]
  exact h.symm

/-- The true spatial derivative, rather than a separately chosen solution,
satisfies the linearized Hamiltonian equation at every valid chart time. -/
theorem radialCoordinateFlow_fderiv_hasDerivAt (g : SmoothMetric M)
    (o : FrameOrientation g) (c d : M) (p : PositiveRadius × UnitTangentBundle g)
    (t : ℝ) (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d).source) :
    HasDerivAt
      (fun s => fderiv ℝ (radialCoordinateFlow g o c d s) (unitRadialCotangentState g c p))
      ((fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g d))
          (unitRadialCotangentState g d (unitTangentRadialFlow g o t p))).comp
        (fderiv ℝ (radialCoordinateFlow g o c d t) (unitRadialCotangentState g c p))) t := by
  let z := unitRadialCotangentState g c p
  let q := unitRadialCotangentState g d (unitTangentRadialFlow g o t p)
  let D := fderiv ℝ (radialCoordinateFlow g o c d t) z
  obtain ⟨F, hfactor⟩ := radialCoordinateFlow_local_factor g o c d p t hc hd
  have hpoint : radialCoordinateFlow g o c d t z = q :=
    radialCoordinateFlow_at_state g o c d t p hc
  have hD : HasFDerivAt (radialCoordinateFlow g o c d t) D z :=
    ((radialFlowContDiffAt_all_time g o t p c d hc hd).differentiableAt (by first | simp | exact_mod_cast le_top)).hasFDerivAt
  have hball : q ∈ Metric.ball q F.radius := Metric.mem_ball_self F.radius_pos
  have hzero : (0 : ℝ) ∈ Ioo (-F.time) F.time :=
    ⟨by linarith [F.time_pos], F.time_pos⟩
  have hspatial (s : ℝ) (hs : s ∈ Ioo (-F.time) F.time) :
      fderiv ℝ (radialCoordinateFlow g o c d (s + t)) z =
        (F.variation (q, s)).comp D := by
    have hFs := F.initial_derivative q hball s hs
    rw [← hpoint] at hFs
    simpa only [hpoint] using ((hFs.comp z hD).congr_of_eventuallyEq (hfactor s hs)).fderiv
  have hvar := F.variation_derivative q hball 0 hzero
  have hcomp := hvar.clm_comp (hasDerivAt_const (0 : ℝ) D)
  have hcomp' : HasDerivAt (fun s => (F.variation (q, s)).comp D)
      ((fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g d)) q).comp D) 0 := by
    simpa only [F.initial q hball, F.initial_variation q hball,
      ContinuousLinearMap.comp_id, ContinuousLinearMap.comp_zero, add_zero] using hcomp
  have heq : (fun s => fderiv ℝ (radialCoordinateFlow g o c d (s + t)) z) =ᶠ[𝓝 0]
      (fun s => (F.variation (q, s)).comp D) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    exact hspatial s hs
  have hshift := hcomp'.congr_of_eventuallyEq heq
  have hshift' : HasDerivAt
      (fun s => fderiv ℝ (radialCoordinateFlow g o c d (s + t)) z)
      ((fderiv ℝ (cotangentHamiltonianField (kineticHamiltonian g d)) q).comp D) (t - t) := by
    simpa only [sub_self] using hshift
  have h := hshift'.comp_sub_const t t
  simpa only [sub_add_cancel] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The position component of the actual variation transforms as a tangent
vector. Its coordinates in a fixed orthonormal frame are chart independent. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem radialCoordinateFlow_position_change_eventually (g : SmoothMetric M)
    (o : FrameOrientation g) (c d₀ d₁ : M) (p : PositiveRadius × UnitTangentBundle g)
    (t : ℝ) (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd₀ : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d₀).source) :
    (fun z => (radialCoordinateFlow g o c d₁ t z).1) =ᶠ[𝓝 (unitRadialCotangentState g c p)]
      (fun z => chartTransition d₀ d₁ (radialCoordinateFlow g o c d₀ t z).1) := by
  have hr := cotangentRadialRetraction_continuousAt g c (unitRadialCotangentState g c p)
    ⟨(chartAt FourSpace c).map_source hc,
      unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have hb : ContinuousAt (fun z : CotangentCoordinates =>
      (unitTangentRadialFlow g o t (cotangentRadialRetraction g c z)).2.base)
      (unitRadialCotangentState g c p) :=
    (continuous_unitTangentBase g).continuousAt.comp
      (continuous_snd.continuousAt.comp ((unitTangentRadialFlow_continuous g o t).continuousAt.comp hr))
  have hd' : (unitTangentRadialFlow g o t
      (cotangentRadialRetraction g c (unitRadialCotangentState g c p))).2.base ∈
      (chartAt FourSpace d₀).source := by
    simpa only [cotangentRadialRetraction_state g c p hc] using hd₀
  filter_upwards [hb.preimage_mem_nhds ((chartAt FourSpace d₀).open_source.mem_nhds hd')] with z hz
  change chartAt FourSpace d₁ _ =
    chartAt FourSpace d₁ ((chartAt FourSpace d₀).symm (chartAt FourSpace d₀ _))
  rw [(chartAt FourSpace d₀).left_inv hz]

theorem radialCoordinateFlow_position_fderiv_change (g : SmoothMetric M)
    (o : FrameOrientation g) (c d₀ d₁ : M) (p : PositiveRadius × UnitTangentBundle g)
    (t : ℝ) (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (hd₀ : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d₀).source)
    (hd₁ : (unitTangentRadialFlow g o t p).2.base ∈ (chartAt FourSpace d₁).source)
    (a : CotangentCoordinates) :
    WithLp.ofLp ((fderiv ℝ (radialCoordinateFlow g o c d₁ t)
      (unitRadialCotangentState g c p) a).1) =
      chartTransitionMatrix d₀ d₁ (chartAt FourSpace d₀ (unitTangentRadialFlow g o t p).2.base) *ᵥ
        WithLp.ofLp ((fderiv ℝ (radialCoordinateFlow g o c d₀ t)
          (unitRadialCotangentState g c p) a).1) := by
  let z := unitRadialCotangentState g c p
  let x := (unitTangentRadialFlow g o t p).2.base
  have hD₀ := ((radialFlowContDiffAt_all_time g o t p c d₀ hc hd₀).differentiableAt
    (by first | simp | exact_mod_cast le_top)).hasFDerivAt
  have hD₁ := ((radialFlowContDiffAt_all_time g o t p c d₁ hc hd₁).differentiableAt
    (by first | simp | exact_mod_cast le_top)).hasFDerivAt
  have hxinv : (chartAt FourSpace d₀).symm (chartAt FourSpace d₀ x) = x :=
    (chartAt FourSpace d₀).left_inv hd₀
  have hφ := ((chartTransition_contDiffAt d₀ d₁ (chartAt FourSpace d₀ x)
    ((chartAt FourSpace d₀).map_source hd₀) (by
      rw [hxinv]
      exact hd₁)).differentiableAt
      (by simp)).hasFDerivAt
  have hpoint : (radialCoordinateFlow g o c d₀ t z).1 = chartAt FourSpace d₀ x :=
    congrArg Prod.fst (radialCoordinateFlow_at_state g o c d₀ t p hc)
  rw [← hpoint] at hφ
  have hcomp := hφ.comp z hD₀.fst
  have hnew := hcomp.congr_of_eventuallyEq
    (radialCoordinateFlow_position_change_eventually g o c d₀ d₁ p t hc hd₀)
  have heval := congrArg (fun L : CotangentCoordinates →L[ℝ] FourSpace => L a)
    (hD₁.fst.unique hnew)
  change (fderiv ℝ (radialCoordinateFlow g o c d₁ t) z a).1 =
    fderiv ℝ (chartTransition d₀ d₁) (radialCoordinateFlow g o c d₀ t z).1
      ((fderiv ℝ (radialCoordinateFlow g o c d₀ t) z a).1) at heval
  rw [hpoint, ← chartTransitionMatrix_mulVec] at heval
  exact congrArg WithLp.ofLp heval

def radialVariationInFrame (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (p : PositiveRadius × UnitTangentBundle g) (t : ℝ)
    (e : FrameBundle g) (a : CotangentCoordinates) : Fin 4 → ℝ :=
  (frameChartMatrix g d e)⁻¹ *ᵥ WithLp.ofLp
    ((fderiv ℝ (radialCoordinateFlow g o c d t) (unitRadialCotangentState g c p) a).1)

theorem radialVariationInFrame_chart_independent (g : SmoothMetric M) (o : FrameOrientation g)
    (c d₀ d₁ : M) (p : PositiveRadius × UnitTangentBundle g) (t : ℝ)
    (e : FrameBundle g) (a : CotangentCoordinates)
    (hc : p.2.base ∈ (chartAt FourSpace c).source)
    (he : e.base = (unitTangentRadialFlow g o t p).2.base)
    (hd₀ : e.base ∈ (chartAt FourSpace d₀).source)
    (hd₁ : e.base ∈ (chartAt FourSpace d₁).source) :
    radialVariationInFrame g o c d₀ p t e a = radialVariationInFrame g o c d₁ p t e a := by
  let E₀ := frameChartMatrix g d₀ e
  let E₁ := frameChartMatrix g d₁ e
  let A := chartTransitionMatrix d₀ d₁ (chartAt FourSpace d₀ e.base)
  let Y₀ := WithLp.ofLp ((fderiv ℝ (radialCoordinateFlow g o c d₀ t)
    (unitRadialCotangentState g c p) a).1)
  let Y₁ := WithLp.ofLp ((fderiv ℝ (radialCoordinateFlow g o c d₁ t)
    (unitRadialCotangentState g c p) a).1)
  have hY : Y₁ = A *ᵥ Y₀ := by
    simpa only [Y₀, Y₁, A, he] using radialCoordinateFlow_position_fderiv_change
      g o c d₀ d₁ p t hc (he ▸ hd₀) (he ▸ hd₁) a
  have hE : A * E₀ = E₁ := frameChartMatrix_change g d₀ d₁ e hd₀ hd₁
  have h₀ : IsUnit E₀.det := Matrix.isUnit_det_of_left_inverse (frameChartMatrix_normalizes g d₀ e hd₀)
  have h₁ : IsUnit E₁.det := Matrix.isUnit_det_of_left_inverse (frameChartMatrix_normalizes g d₁ e hd₁)
  have hvec : E₁ *ᵥ (E₀⁻¹ *ᵥ Y₀) = Y₁ := by
    rw [← hE, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ h₀, Matrix.mul_one, hY]
  change E₀⁻¹ *ᵥ Y₀ = E₁⁻¹ *ᵥ Y₁
  rw [← hvec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h₁, Matrix.one_mulVec]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Mixed-direction integration by parts for the actual two-form jet. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Identification of the actual global normal variation with the matrix
Jacobi solution, with its initial data derived from vertical momentum. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T2Space M] [CompactSpace M]

theorem radialCoordinateFlow_self_zero_fderiv (g : SmoothMetric M)
    (o : FrameOrientation g) (c : M) (p : PositiveRadius × UnitTangentBundle g)
    (hc : p.2.base ∈ (chartAt FourSpace c).source) :
    fderiv ℝ (radialCoordinateFlow g o c c 0) (unitRadialCotangentState g c p) =
      ContinuousLinearMap.id ℝ CotangentCoordinates := by
  have hz : {z : CotangentCoordinates | z.1 ∈ (chartAt FourSpace c).target ∧ z.2 ≠ 0}
      ∈ 𝓝 (unitRadialCotangentState g c p) :=
    (((chartAt FourSpace c).open_target.preimage continuous_fst).inter
      (isOpen_compl_singleton.preimage continuous_snd)).mem_nhds
        ⟨(chartAt FourSpace c).map_source hc,
          unitCotangentState_momentum_ne_zero g c p.1.val p.1.property p.2 hc⟩
  have heq : radialCoordinateFlow g o c c 0 =ᶠ[𝓝 (unitRadialCotangentState g c p)] id := by
    filter_upwards [hz] with z hz
    rw [radialCoordinateFlow, unitTangentRadialFlow_zero,
      unitRadialCotangentState_retraction g c z hz]
    rfl
  exact ((hasFDerivAt_id (unitRadialCotangentState g c p)).congr_of_eventuallyEq heq).fderiv

end
end PositiveEinsteinFour.Geometry
end


section

/-! Mixed integration by parts turns the first-order cross terms into
the actual curvature action on two-forms. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

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

theorem radialCoordinateFlow_frame_endpoint_time (g : SmoothMetric M) (o : FrameOrientation g)
    (c d : M) (e : FrameBundle g) (he : e.base ∈ (chartAt FourSpace c).source)
    (t : ℝ) (ht : 0 < t) (v : FourSpace) (hv : v ≠ 0) :
    (radialCoordinateFlow g o c d t
      (chartAt FourSpace c e.base, frameMomentumMap g c e v)).1 =
      chartAt FourSpace d (frameExponential g o e (t • v)) := by
  let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
  let q := (euclideanPolarHomeomorph w).1
  let r := (euclideanPolarHomeomorph w).2
  have hvr : r.val • q.val = v :=
    congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
  have hstate : unitRadialCotangentState g c (r, unitTangentTurn e q) =
      (chartAt FourSpace c e.base, frameMomentumMap g c e v) := by
    change unitCotangentState g c r.val (unitTangentTurn e q) = _
    rw [unitCotangentState_turn g c e he, hvr]
  rw [← hstate, radialCoordinateFlow_at_state g o c d t _ he]
  change chartAt FourSpace d (unitTangentFlowMap g o (r.val * t) (unitTangentTurn e q)).base = _
  rw [← hvr, smul_smul]
  have h := frameExponential_radial g o e q ⟨t * r.val, mul_pos ht r.property⟩
  simpa only [unitGeodesic, mul_comm] using congrArg (chartAt FourSpace d) h.symm

omit [T2Space M] [CompactSpace M] in
theorem frameMomentumMap_apply (g : SmoothMetric M) (c : M) (e : FrameBundle g)
    (he : e.base ∈ (chartAt FourSpace c).source) (v : FourSpace) :
    frameMomentumMap g c e v = WithLp.toLp 2
      (metricInChart g c (chartAt FourSpace c e.base) *ᵥ
        (frameChartMatrix g c e *ᵥ WithLp.ofLp v)) := by
  let Q := (chartForwardOperator c e.base).comp e.frame.map.toContinuousLinearMap
  have hcol (i : Fin 4) : Q (coordinateVector i) =
      WithLp.toLp 2 (fun j => frameChartMatrix g c e j i) := by
    change chartForwardOperator c e.base (e.frame.map (coordinateVector i)) = _
    rw [e.frame.map_coordinateVector]
    exact (frameChart_column_eq_derivative g c e i he).symm
  have hQ : Q v = WithLp.toLp 2 (frameChartMatrix g c e *ᵥ WithLp.ofLp v) := by
    have hsum : (∑ i, (WithLp.ofLp v) i • coordinateVector i) = v :=
      sum_coordinateVector (WithLp.ofLp v)
    conv_lhs => rw [← hsum]
    rw [map_sum]
    simp only [map_smul, hcol]
    ext j
    simp [Matrix.mulVec, dotProduct, mul_comm]
  change Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)
    (metricInChart g c (chartAt FourSpace c e.base)) (Q v) = _
  rw [hQ]
  rfl

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

def frameFullInitialVariation (g : SmoothMetric M) (e : FrameBundle g)
    (w : Fin 4 → ℝ) : CotangentCoordinates :=
  (0, WithLp.toLp 2
    (metricInChart g e.base (chartAt FourSpace e.base e.base) *ᵥ
      (frameChartMatrix g e.base e *ᵥ w)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual exterior-derivative and codifferential energy of a smooth
two-form, and its integrated Weitzenböck identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_5 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

omit [T3Space M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [Nonempty M] in
theorem integral_frame_sum_three (μ : Measure (FrameBundle g))
    (F : Fin 4 → Fin 4 → Fin 4 → FrameBundle g → ℝ)
    (hF : ∀ i j k, Integrable (F i j k) μ) :
    (∫ e, ∑ i, ∑ j, ∑ k, F i j k e ∂μ) = ∑ i, ∑ j, ∑ k, ∫ e, F i j k e ∂μ := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    integrable_finsetSum _ fun k _ => hF i j k)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => hF i j k)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_finsetSum _ (fun k _ => hF i j k)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The integrated Weitzenböck identity for the actual smooth two-forms
on a closed Einstein four-manifold. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

local instance instCompactSpaceFrameBundle_6 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

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

theorem frameExponential_first_ray (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t) :
    frameExponential g o e (t • coordinateVector 0) = (parallelFrameFlowMap g 0 t e).base := by
  have hu : unitTangentTurn e firstDirection = unitTangentOfFrame e := by
    apply unitTangent_ext (u := unitTangentTurn e firstDirection) (v := unitTangentOfFrame e) rfl
    exact (e.frame.turn_first firstDirection).trans (e.frame.map_coordinateVector 0)
  have h := frameExponential_radial g o e firstDirection ⟨t, ht⟩
  change frameExponential g o e (t • coordinateVector 0) =
    unitGeodesic g o (unitTangentTurn e firstDirection) t at h
  rw [hu, unitGeodesic, unitTangentFlowMap_of_frame g o t e he] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The exponential commutes with oriented orthogonal changes of its initial frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular Matrix Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem unitTangentTurn_rotate (g : SmoothMetric M) (e : FrameBundle g)
    (Q : OrientedOrthogonalFour) (q : Directions) :
    unitTangentTurn (e.rotate (orientedToOrthogonal Q)) q =
      unitTangentTurn e (orientedDirection Q q) := by
  calc
    _ = unitTangentOfFrame ((e.rotate (orientedToOrthogonal Q)).rotate
        (orientedToOrthogonal (directionOrientedMatrix q))) := rfl
    _ = unitTangentOfFrame (e.rotate (orientedToOrthogonal (Q * directionOrientedMatrix q))) :=
      congrArg unitTangentOfFrame (frameRotate_mul e Q (directionOrientedMatrix q))
    _ = unitTangentTurn e (orientedDirection (Q * directionOrientedMatrix q) firstDirection) :=
      (unitTangentTurn_first e (Q * directionOrientedMatrix q)).symm
    _ = unitTangentTurn e (orientedDirection Q q) := by
      rw [orientedDirection_mul, orientedDirection_completion]

variable [T2Space M] [CompactSpace M]

theorem frameExponential_rotate (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (Q : OrientedOrthogonalFour) (v : FourSpace) :
    frameExponential g o (e.rotate (orientedToOrthogonal Q)) v =
      frameExponential g o e (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
        (orientedToOrthogonal Q).property v) := by
  let L := orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property
  by_cases hv : v = 0
  · subst v
    rw [map_zero, frameExponential_zero, frameExponential_zero]
    rfl
  · let w : ({0}ᶜ : Set FourSpace) := ⟨v, hv⟩
    let q := (euclideanPolarHomeomorph w).1
    let r := (euclideanPolarHomeomorph w).2
    let q' := orientedDirection Q q
    have hvr : r.val • q.val = v :=
      congrArg Subtype.val (euclideanPolarHomeomorph.symm_apply_apply w)
    calc
      _ = frameExponential g o (e.rotate (orientedToOrthogonal Q)) (r.val • q.val) := by rw [hvr]
      _ = unitGeodesic g o (unitTangentTurn (e.rotate (orientedToOrthogonal Q)) q) r.val :=
        frameExponential_radial g o (e.rotate (orientedToOrthogonal Q)) q r
      _ = unitGeodesic g o (unitTangentTurn e q') r.val := by
        rw [unitTangentTurn_rotate g e Q q]
      _ = frameExponential g o e (r.val • q'.val) := (frameExponential_radial g o e q' r).symm
      _ = frameExponential g o e (L v) := by
        rw [← hvr, map_smul]
        congr 1

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

theorem frameExponential_rotate_mfderiv (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (Q : OrientedOrthogonalFour) (v w : FourSpace) :
    mfderiv I4 I4 (frameExponential g o (e.rotate (orientedToOrthogonal Q))) v w =
      mfderiv I4 I4 (frameExponential g o e)
        (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property v)
        (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property w) := by
  let L := (orthogonalEuclideanIsometry (orientedToOrthogonal Q).val (orientedToOrthogonal Q).property).toContinuousLinearEquiv
  have hL : HasFDerivAt (fun w : FourSpace => L w) (L : FourSpace →L[ℝ] FourSpace) v :=
    (L : FourSpace →L[ℝ] FourSpace).hasFDerivAt
  have he := (frameExponential_contMDiff g o e).mdifferentiable one_ne_zero (L v)
  have h := congrArg (fun A => A w) (mfderiv_comp v he hL.differentiableAt.mdifferentiableAt)
  have heq : frameExponential g o (e.rotate (orientedToOrthogonal Q)) =
      (fun w : FourSpace => frameExponential g o e (L w)) :=
    funext (frameExponential_rotate g o e Q)
  have hDL : mfderiv I4 I4 (fun z : FourSpace => L z) v w = L w := by
    rw [mfderiv_eq_fderiv, hL.fderiv]
    rfl
  change mfderiv I4 I4 (fun z => frameExponential g o e (L z)) v w =
    mfderiv I4 I4 (frameExponential g o e) (L v)
      (mfderiv I4 I4 (fun z : FourSpace => L z) v w) at h
  rw [← heq, hDL] at h
  exact h

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

theorem heatTwoFormConnectionMatrix_action (B : Mat4) (a : TwoFormFour) :
    heatTwoFormConnectionMatrix B *ᵥ WithLp.ofLp a =
      WithLp.ofLp (twoFormSkewAction (twoFormExtract B) a) := by
  ext k
  fin_cases k <;>
    simp [heatTwoFormConnectionMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, twoFormSkewAction, EuclideanSpace.basisFun_apply] <;> ring

theorem heatTwoFormConnectionMatrix_skew (B : Mat4) :
    (heatTwoFormConnectionMatrix B)ᵀ = -heatTwoFormConnectionMatrix B := by
  ext k l
  have h := twoFormSkewAction_skewAdjoint (twoFormExtract B)
    (EuclideanSpace.basisFun (Fin 6) ℝ k) (EuclideanSpace.basisFun (Fin 6) ℝ l)
  simpa only [EuclideanSpace.inner_basisFun_real, EuclideanSpace.basisFun_inner,
    heatTwoFormConnectionMatrix, Matrix.transpose_apply, Matrix.neg_apply] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual Weitzenböck curvature potential in the normal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem heatNormalFrameCurvature_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ n P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (v : Fin 4 → Fin 4) :
    ContDiffAt ℝ n (fun y => heatNormalFrameCurvature g c P y v) x := by
  have hE (i j : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hR (w : Fin 4 → Fin 4) :
      ContDiffAt ℝ n (fun y => curvatureCoordinates g c (P y).1 w) x := by
    exact ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun z => curvatureCoordinates g c z w) x
      ((curvatureCoordinates_contDiffAt g c (P x).1 hx
        (metricInChart_posDef g c (P x).1 hx).det_pos.ne' w).of_le (by first | simp | exact_mod_cast le_top)) hP.fst
  unfold heatNormalFrameCurvature frameTensor
  apply ContDiffAt.sum
  intro w _
  exact (contDiffAt_prod fun i _ => hE (w i) (v i)).mul (hR w)

theorem heatNormalPotential_contDiffAt (n : ℕ) (g : SmoothMetric M) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ n P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (k l : Fin 6) : ContDiffAt ℝ n (fun y => heatNormalPotential g c P y k l) x := by
  change ContDiffAt ℝ n (fun y =>
    6 * (1 : TwoFormMatrix) k l - 2 * -heatNormalFrameCurvature g c P y
      ![(AlgebraicCurvature.pair k).1, (AlgebraicCurvature.pair k).2,
        (AlgebraicCurvature.pair l).1, (AlgebraicCurvature.pair l).2]) x
  exact contDiffAt_const.sub (contDiffAt_const.mul
    (heatNormalFrameCurvature_contDiffAt n g c P x hP hx _).neg)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual smooth two-forms expressed in the normal frame. Regularity is
proved from their coordinate tensors, without differentiating a chosen
global reference frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_extract_twoFormTensor (a : TwoFormFour) :
    twoFormExtractLinear (twoTensorMatrixLinear (twoFormTensor a)) = a := by
  ext k
  fin_cases k <;> rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def heatNormalTwoFormValue (o : FrameOrientation g) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (u : M → TwoFormFour) (x : FourSpace) : TwoFormFour :=
  twoFormExtractLinear (twoTensorMatrixLinear
    (frameTensor (P x).2 (twoFormCoordinates o u c (P x).1)))

theorem heatNormalTwoFormValue_tensor (o : FrameOrientation g) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (u : M → TwoFormFour) (x : FourSpace) :
    twoFormTensor (heatNormalTwoFormValue o c P u x) =
      frameTensor (P x).2 (twoFormCoordinates o u c (P x).1) := by
  let p := (chartAt FourSpace c).symm (P x).1
  let A := (o.frame p).matrix⁻¹ * chartInverseMatrix c (P x).1 * (P x).2
  have hrep : frameTensor (P x).2 (twoFormCoordinates o u c (P x).1) =
      twoFormTensor (twoFormFrameAction A (u p)) := by
    unfold twoFormCoordinates twoFormTensorAt
    rw [← frameTensor_mul, ← frameTensor_mul]
    simpa only [A, p, Matrix.mul_assoc] using (twoFormTensor_frameAction A (u p)).symm
  unfold heatNormalTwoFormValue
  rw [hrep, heat_extract_twoFormTensor]

theorem heatNormalTwoFormValue_contDiffAt (n : ℕ) {o : FrameOrientation g}
    {u : M → TwoFormFour} (hu : TwoFormSmooth o u) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (x : FourSpace) (hP : ContDiffAt ℝ n P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target) :
    ContDiffAt ℝ n (heatNormalTwoFormValue o c P u) x := by
  have hE (i j : Fin 4) : ContDiffAt ℝ n (fun y => (P y).2 i j) x :=
    contDiffAt_pi.mp (contDiffAt_pi.mp hP.snd i) j
  have hT (v : Fin 2 → Fin 4) :
      ContDiffAt ℝ n (fun y => twoFormCoordinates o u c (P y).1 v) x :=
    ContDiffAt.comp (f := fun y => (P y).1)
      (g := fun z => twoFormCoordinates o u c z v) x
      ((hu.coordinates_contDiffAt c (P x).1 hx v).of_le (by first | simp | exact_mod_cast le_top)) hP.fst
  have hFT : ContDiffAt ℝ n
      (fun y => frameTensor (P y).2 (twoFormCoordinates o u c (P y).1)) x := by
    apply contDiffAt_pi.mpr
    intro v
    unfold frameTensor
    apply ContDiffAt.sum
    intro w _
    exact (contDiffAt_prod fun i _ => hE (w i) (v i)).mul (hT w)
  let L := (twoFormExtractLinear.comp twoTensorMatrixLinear).toContinuousLinearMap
  exact L.contDiff.contDiffAt.comp x hFT

end
end PositiveEinsteinFour.Geometry
end


section

/-! The normal-frame first-order expression is the pullback of the
actual Levi-Civita derivative of a smooth two-form. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

def heatNormalTwoFormNabla (o : FrameOrientation g) (c : M)
    (P : FourSpace → CoordinateFrameSpace) (u : M → TwoFormFour) (i : Fin 4)
    (x : FourSpace) : TwoFormFour :=
  fderiv ℝ (heatNormalTwoFormValue o c P u) x (coordinateVector i) +
    twoFormSkewAction (twoFormExtract (heatNormalFrameConnection g c P i x))
      (heatNormalTwoFormValue o c P u x)

theorem heatNormalTwoFormNabla_tensor {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ 1 P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i : Fin 4) :
    frameTensor (P x).2 (∑ r : Fin 4, (fderiv ℝ P x (coordinateVector i)).1 r •
      tensorCovariantDirection (connectionMatrix g c) (twoFormCoordinates o u c) r (P x).1) =
      twoFormTensor (heatNormalTwoFormNabla o c P u i x) := by
  have hPd := hP.differentiableAt one_ne_zero
  have ha : DifferentiableAt ℝ (heatNormalTwoFormValue o c P u) x :=
    (heatNormalTwoFormValue_contDiffAt 1 hu c P x hP hx).differentiableAt one_ne_zero
  have hT (v : Fin 2 → Fin 4) :
      DifferentiableAt ℝ (fun z => twoFormCoordinates o u c z v) (P x).1 :=
    (hu.coordinates_contDiffAt c (P x).1 hx v).differentiableAt (by first | simp | exact_mod_cast le_top)
  have h := heatNormal_covariant_pullback g c P (twoFormCoordinates o u c) x
    hPd hT hG.self_of_nhds i
  have hrep : (fun y => frameTensor (P y).2 (twoFormCoordinates o u c (P y).1)) =
      (fun y => twoFormTensor (heatNormalTwoFormValue o c P u y)) := by
    funext y
    exact (heatNormalTwoFormValue_tensor o c P u y).symm
  rw [hrep] at h
  change tensorPartial (fun y => twoFormTensor (heatNormalTwoFormValue o c P u y)) i x -
      tensorSlotAction (heatNormalFrameConnection g c P i x)
        (twoFormTensor (heatNormalTwoFormValue o c P u x)) = _ at h
  rw [tensorPartial_twoForm ha] at h
  have hsk := heatNormalFrameConnection_skew g c P x hPd hx hG i
  rw [← twoFormMatrix_extract _ hsk, tensorSlotAction_twoForm, sub_neg_eq_add] at h
  exact ((twoFormTensorLinear.map_add _ _).trans h).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! A continuous intrinsic Jacobian density for the actual exponential.
Its expression in any output chart is the metric density times the
absolute coordinate determinant. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Bundle Set
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponentialJacobian_nonneg (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v : FourSpace) : 0 ≤ frameExponentialJacobian g o e v :=
  Real.sqrt_nonneg _

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

/-! First and second coordinate derivatives under a fixed affine change of
four-dimensional coordinates, used for rescaling the actual scalar operator. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped ContDiff BigOperators

noncomputable section

def scalarAffineMap (C : Mat4) (q : FourSpace) (z : FourSpace) : FourSpace :=
  (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) C z + q

theorem scalarAffineMap_hasFDerivAt (C : Mat4) (q z : FourSpace) :
    HasFDerivAt (scalarAffineMap C q)
      ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) C) z := by
  exact ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) C).hasFDerivAt.add_const q

theorem scalarAffineMap_jacobian (C : Mat4) (q z : FourSpace) :
    jacobianMatrix (scalarAffineMap C q) z = C := by
  ext a i
  change ((fderiv ℝ (scalarAffineMap C q) z) (coordinateVector i)) a = C a i
  rw [(scalarAffineMap_hasFDerivAt C q z).fderiv]
  change (C *ᵥ WithLp.ofLp (coordinateVector i)) a = _
  simp [coordinateVector, Matrix.mulVec, dotProduct, PiLp.single_apply]

theorem scalarAffineMap_partial (C : Mat4) (q z : FourSpace) (ψ : FourSpace → ℝ)
    (hψ : DifferentiableAt ℝ ψ (scalarAffineMap C q z)) (i : Fin 4) :
    partialDeriv (fun w => ψ (scalarAffineMap C q w)) i z =
      ∑ a, C a i * partialDeriv ψ a (scalarAffineMap C q z) := by
  rw [partialDeriv_comp (scalarAffineMap_hasFDerivAt C q z).differentiableAt hψ,
    scalarAffineMap_jacobian]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual metric coefficients put the chart Laplacian in divergence
form.  This supplies the coefficient identity for local energy estimates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem partialDeriv_chartVolumeDensity (g : SmoothMetric M) (c : M)
    (z : FourSpace) (hz : z ∈ (chartAt FourSpace c).target) (i : Fin 4) :
    partialDeriv (chartVolumeDensity g c) i z =
      (∑ k, christoffel g c z k i k) * chartVolumeDensity g c z := by
  let x : ℝ → FourSpace := fun t => z + t • coordinateVector i
  have hx : HasDerivAt x (coordinateVector i) 0 := by
    simpa only [x, one_smul, id_eq] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (coordinateVector i)).const_add z
  have hz₀ : x 0 = z := by simp [x]
  have h₁ := hasDerivAt_chartVolumeDensity g c x (fun r => coordinateVector i r)
    0 (hz₀.symm ▸ hz) (by simpa using hx)
  have h₂ := (chartVolumeDensity_contDiffAt g c z hz).differentiableAt (by first | simp | exact_mod_cast le_top)
  have h₃ := hasDerivAt_coordinate_comp hx (hz₀.symm ▸ h₂)
  have he := h₃.unique h₁
  simpa [hz₀, coordinateVector, PiLp.single_apply,
    connectionMatrix, Matrix.trace, Matrix.sum_apply, Matrix.smul_apply] using he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Exact Lebesgue scaling and L² pullback for the affine coordinates used
to freeze the metric at a chart point. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped ENNReal

noncomputable section

def scalarAffineJacobian (A : FourSpace ≃L[ℝ] FourSpace) : ℝ :=
  |(LinearMap.det A.toLinearMap)⁻¹|

theorem scalarAffineJacobian_pos (A : FourSpace ≃L[ℝ] FourSpace) :
    0 < scalarAffineJacobian A := by
  exact abs_pos.mpr (inv_ne_zero (A.toLinearEquiv.isUnit_det'.ne_zero))

theorem scalarAffine_map_volume (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace) :
    Measure.map (fun x => A x + q) (volume : Measure FourSpace) =
      ENNReal.ofReal (scalarAffineJacobian A) • volume := by
  have hA : Measure.map A (volume : Measure FourSpace) =
      ENNReal.ofReal (scalarAffineJacobian A) • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume A.toLinearEquiv.isUnit_det'.ne_zero
  change Measure.map ((fun x : FourSpace => x + q) ∘ A) volume = _
  rw [← Measure.map_map (by fun_prop) A.continuous.measurable, hA,
    Measure.map_smul, map_add_right_eq_self]

theorem scalarAffine_integral (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    (f : FourSpace → ℝ) :
    (∫ x, f (A x + q)) = scalarAffineJacobian A * ∫ x, f x := by
  have he : MeasurableEmbedding (fun x => A x + q) :=
    (A.toHomeomorph.trans (Homeomorph.addRight q)).measurableEmbedding
  rw [← he.integral_map, scalarAffine_map_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (scalarAffineJacobian_pos A).le, smul_eq_mul]

theorem scalarAffine_memLp (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    {f : FourSpace → ℝ} (hf : MemLp f 2 (volume : Measure FourSpace)) :
    MemLp (fun x => f (A x + q)) 2 volume := by
  have hscaled := hf.smul_measure (c := ENNReal.ofReal (scalarAffineJacobian A))
    ENNReal.ofReal_ne_top
  rw [← scalarAffine_map_volume A q] at hscaled
  exact hscaled.comp_of_map (by fun_prop)

def scalarAffinePullbackL2 (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    (f : Lp ℝ 2 (volume : Measure FourSpace)) : Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarAffine_memLp A q (Lp.memLp f)).toLp _

theorem scalarAffinePullbackL2_coe (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    (f : Lp ℝ 2 (volume : Measure FourSpace)) :
    scalarAffinePullbackL2 A q f =ᵐ[volume] (fun x => f (A x + q)) :=
  MemLp.coeFn_toLp (scalarAffine_memLp A q (Lp.memLp f))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual invertible affine map used to rescale a metric chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frozenFrameLinearEquiv_symm_matrix (g : SmoothMetric M) (c : M)
    (z₀ : ChartTarget c) :
    (frozenFrameLinearEquiv g c z₀).symm.toContinuousLinearMap =
      (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) (chartGramMatrix g c 1 z₀)⁻¹ := by
  apply ContinuousLinearMap.ext
  intro v
  apply (frozenFrameLinearEquiv g c z₀).injective
  change (frozenFrameLinearEquiv g c z₀) ((frozenFrameLinearEquiv g c z₀).symm v) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change v = (Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) (chartGramMatrix g c 1 z₀)
    ((Matrix.toEuclideanCLM (n := Fin 4) (𝕜 := ℝ)) (chartGramMatrix g c 1 z₀)⁻¹ v)
  rw [← mul_apply_eq_comp, ← map_mul, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (chartGramMatrix_isUnit g c z₀)), map_one]
  rfl

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

/-! Local division by a smooth positive density at Sobolev order two. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric Filter
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

def densityCutoffL2 (φ : S) (w : L2) : L2 :=
  scalarL2Multiply (φ.toLp ∞ volume) w

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded localization of the intrinsic scalar H¹ space into Euclidean
L⁴. The construction uses the actual chart representative and its four
weak derivatives, with a compact smooth cutoff. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff ENNReal

noncomputable section

local instance instFactLeENNRealOfNat_solutions_3_r3665a6_1 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance localSobolev_frameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! Affine pullback of the actual L2 function preserves first-order Sobolev
regularity.  The derivative identity is proved by changing variables in
Schwartz test integrals. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

theorem scalarAffine_complex_integral (A : V ≃L[ℝ] V) (q : V)
    (f : V → ℂ) :
    (∫ x, f (A x + q)) = (scalarAffineJacobian A : ℂ) * ∫ x, f x := by
  have he : MeasurableEmbedding (fun x => A x + q) :=
    (A.toHomeomorph.trans (Homeomorph.addRight q)).measurableEmbedding
  rw [← he.integral_map, scalarAffine_map_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (scalarAffineJacobian_pos A).le]
  simp only [Complex.real_smul]

theorem scalarAffine_complex_memLp (A : V ≃L[ℝ] V) (q : V)
    {f : V → ℂ} (hf : MemLp f 2 (volume : Measure V)) :
    MemLp (fun x => f (A x + q)) 2 volume := by
  have hscaled := hf.smul_measure (c := ENNReal.ofReal (scalarAffineJacobian A))
    ENNReal.ofReal_ne_top
  rw [← scalarAffine_map_volume A q] at hscaled
  exact hscaled.comp_of_map (by fun_prop)

/-- Pullback of the complex L2 representative by an invertible affine map. -/
def scalarComplexAffinePullbackL2 (A : V ≃L[ℝ] V) (q : V) (u : L2) : L2 :=
  (scalarAffine_complex_memLp A q (Lp.memLp u)).toLp _

theorem scalarComplexAffinePullbackL2_coe (A : V ≃L[ℝ] V) (q : V) (u : L2) :
    scalarComplexAffinePullbackL2 A q u =ᵐ[volume] fun x => u (A x + q) :=
  MemLp.coeFn_toLp (scalarAffine_complex_memLp A q (Lp.memLp u))

/-- Inverse affine coordinates on test functions. -/
def scalarAffineTestCLM (A : V ≃L[ℝ] V) (q : V) : S →L[ℂ] S :=
  (SchwartzMap.compSubConstCLM ℂ q).comp
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm)

theorem scalarAffineTestCLM_apply (A : V ≃L[ℝ] V) (q : V) (φ : S) (x : V) :
    scalarAffineTestCLM A q φ x = φ (A.symm (x - q)) := rfl

theorem scalarAffineTestCLM_derivative (A : V ≃L[ℝ] V) (q v : V) (φ : S) :
    ∂_{A v} (scalarAffineTestCLM A q φ) = scalarAffineTestCLM A q (∂_{v} φ) := by
  ext x
  change (fderiv ℝ (fun y => ((φ : V → ℂ) ∘ A.symm) (y - q)) x) (A v) =
    (fderiv ℝ φ (A.symm (x - q))) v
  rw [fderiv_comp_sub]
  change (fderiv ℝ ((φ : V → ℂ) ∘ A.symm) (x - q)) (A v) = _
  rw [_root_.fderiv_comp (x - q) φ.differentiableAt A.symm.differentiableAt,
    A.symm.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- Distributional affine pullback, with its change-of-variables Jacobian. -/
def scalarAffineDistribution (A : V ≃L[ℝ] V) (q : V) : T →L[ℂ] T :=
  (scalarAffineJacobian A : ℂ) • PointwiseConvergenceCLM.precomp ℂ
    (scalarAffineTestCLM A q)

theorem scalarAffineDistribution_apply (A : V ≃L[ℝ] V) (q : V) (u : T) (φ : S) :
    scalarAffineDistribution A q u φ =
      (scalarAffineJacobian A : ℂ) * u (scalarAffineTestCLM A q φ) := rfl

theorem scalarAffineDistribution_L2 (A : V ≃L[ℝ] V) (q : V) (u : L2) :
    scalarAffineDistribution A q (u : T) = (scalarComplexAffinePullbackL2 A q u : T) := by
  ext φ
  rw [scalarAffineDistribution_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  change (scalarAffineJacobian A : ℂ) *
    (∫ x, scalarAffineTestCLM A q φ x * u x) =
      ∫ x, φ x * scalarComplexAffinePullbackL2 A q u x
  rw [integral_congr_ae (show (fun x => φ x * scalarComplexAffinePullbackL2 A q u x) =ᵐ[volume]
      (fun x => φ x * u (A x + q)) from
    (scalarComplexAffinePullbackL2_coe A q u).mono fun x hx => congrArg (φ x * ·) hx)]
  have h := scalarAffine_complex_integral A q
    (fun x => scalarAffineTestCLM A q φ x * u x)
  simpa only [scalarAffineTestCLM_apply, add_sub_cancel_right,
    ContinuousLinearEquiv.symm_apply_apply] using h.symm

/-- The weak derivative is transformed by the actual linear part A. -/
theorem scalarAffineDistribution_derivative (A : V ≃L[ℝ] V) (q v : V) (u : T) :
    ∂_{v} (scalarAffineDistribution A q u) =
      scalarAffineDistribution A q (∂_{A v} u) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    scalarAffineDistribution_apply, map_neg, scalarAffineTestCLM_derivative, mul_neg]

theorem scalarAffineDistribution_memSobolev_zero (A : V ≃L[ℝ] V) (q : V)
    (u : T) (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (scalarAffineDistribution A q u) := by
  obtain ⟨f, hf⟩ := memSobolev_zero_iff.mp hu
  apply memSobolev_zero_iff.mpr
  exact ⟨scalarComplexAffinePullbackL2 A q f, hf ▸ scalarAffineDistribution_L2 A q f⟩

/-- First-order Sobolev regularity is stable under an invertible affine
change of coordinates, with no smoothness assumption on the L2 function. -/
theorem scalarAffineDistribution_memSobolev_one (A : V ≃L[ℝ] V) (q : V)
    (u : T) (hu : MemSobolev 1 2 u) :
    MemSobolev 1 2 (scalarAffineDistribution A q u) := by
  have hcriterion := scalar_memSobolev_succ_iff 0 (scalarAffineDistribution A q u)
  rw [zero_add] at hcriterion
  apply hcriterion.mpr
  refine ⟨scalarAffineDistribution_memSobolev_zero A q u (hu.mono (by norm_num)), ?_⟩
  intro i
  change MemSobolev 0 2
    (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (scalarAffineDistribution A q u))
  rw [scalarAffineDistribution_derivative]
  exact scalarAffineDistribution_memSobolev_zero A q _
    (by simpa only [sub_self] using hu.lineDerivOp (m := A (EuclideanSpace.basisFun (Fin 4) ℝ i)))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Integer Sobolev regularity under the actual affine chart map.
All orders are needed for the smooth harmonic representative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)

theorem scalarAffineDistribution_memSobolev_integer (n : ℕ) (A : V ≃L[ℝ] V) (q : V)
    (u : T) (hu : MemSobolev (n : ℝ) 2 u) :
    MemSobolev (n : ℝ) 2 (scalarAffineDistribution A q u) := by
  induction n generalizing u with
  | zero =>
      simp only [Nat.cast_zero] at hu ⊢
      exact scalarAffineDistribution_memSobolev_zero A q u hu
  | succ n ih =>
      rw [Nat.cast_succ] at hu ⊢
      apply (scalar_memSobolev_succ_iff (n : ℝ) _).mpr
      refine ⟨ih u (hu.mono (by linarith)), ?_⟩
      intro i
      change MemSobolev (n : ℝ) 2
        (∂_{EuclideanSpace.basisFun (Fin 4) ℝ i} (scalarAffineDistribution A q u))
      rw [scalarAffineDistribution_derivative]
      apply ih
      simpa only [add_sub_cancel_right] using
        hu.lineDerivOp (m := A (EuclideanSpace.basisFun (Fin 4) ℝ i))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The ordinary continuous H¹-to-L⁴ embedding for the actual compact
four-manifold, assembled from compact chart cutoffs. No sharp constant is
asserted here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instFactLeENNRealOfNat_solutions_6
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance manifoldSobolev_frameCompact_r3665a6_1 (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
local instance manifoldSobolev_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactness of each compact chart localization of the intrinsic scalar
H¹ space. The actual first jet lies in the closed Euclidean graph, with
support in the fixed compact set, so Euclidean Rellich applies. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped Manifold ContDiff ENNReal

noncomputable section

local instance instMeasurableSpaceFourSpace : MeasurableSpace FourSpace := borel FourSpace
local instance instBorelSpaceFourSpace : BorelSpace FourSpace := ⟨rfl⟩
local instance instMeasureSpaceFourSpace : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance rellichLocalization_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

end
end PositiveEinsteinFour.Geometry
end


section

/-! The same weighted H1 representative satisfies the actual geometric
equation after the invertible frozen-frame change of coordinates. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff BigOperators

noncomputable section

theorem scalarAffineL2_integral (A : FourSpace ≃L[ℝ] FourSpace) (q : FourSpace)
    (w : Lp ℝ 2 (volume : Measure FourSpace)) (ψ : FourSpace → ℝ) :
    (∫ y, scalarAffinePullbackL2 A q w y * ψ y) =
      scalarAffineJacobian A * ∫ z, w z * ψ (A.symm (z - q)) := by
  rw [integral_congr_ae ((scalarAffinePullbackL2_coe A q w).mono
    (fun y hy => congrArg (· * ψ y) hy))]
  have h := scalarAffine_integral A q (fun z => w z * ψ (A.symm (z - q)))
  simpa only [add_sub_cancel_right, ContinuousLinearEquiv.symm_apply_apply] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Spatial derivatives of a jointly C2 time-space function are jointly
continuous on their actual open domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Filter
open scoped ContDiff _root_.Topology

noncomputable section

theorem fourHeat_slice_partial (F : ℝ × FourSpace → ℝ) (z : ℝ × FourSpace)
    (hF : DifferentiableAt ℝ F z) (i : Fin 4) :
    partialDeriv (fun x => F (z.1, x)) i z.2 =
      fderiv ℝ F z (0, coordinateVector i) := by
  have he := (hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have h := hF.hasFDerivAt.comp z.2 he
  change HasFDerivAt (fun x => F (z.1, x)) _ z.2 at h
  unfold partialDeriv
  rw [h.fderiv]
  rfl

theorem fourHeat_slice_partial_contDiffAt (F : ℝ × FourSpace → ℝ) (z : ℝ × FourSpace)
    (hF : ContDiffAt ℝ 2 F z) (i : Fin 4) :
    ContDiffAt ℝ 1 (fun w : ℝ × FourSpace => partialDeriv (fun x => F (w.1, x)) i w.2) z := by
  have hC : ContDiffAt ℝ 1 (fun w => fderiv ℝ F w (0, coordinateVector i)) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  apply hC.congr_of_eventuallyEq
  filter_upwards [hF.eventually (by norm_num)] with w hw
  exact fourHeat_slice_partial F w (hw.differentiableAt (by norm_num)) i

theorem fourHeat_slice_partial_continuousAt (F : ℝ × FourSpace → ℝ) (z : ℝ × FourSpace)
    (hF : ContDiffAt ℝ 1 F z) (i : Fin 4) :
    ContinuousAt (fun w : ℝ × FourSpace => partialDeriv (fun x => F (w.1, x)) i w.2) z := by
  have hC : ContDiffAt ℝ 0 (fun w => fderiv ℝ F w (0, coordinateVector i)) z :=
    (hF.fderiv_right (m := 0) (by norm_num)).clm_apply contDiffAt_const
  apply hC.continuousAt.congr_of_eventuallyEq
  filter_upwards [hF.eventually (by norm_num)] with w hw
  exact fourHeat_slice_partial F w (hw.differentiableAt (by norm_num)) i

theorem fourHeat_slice_second_continuousAt (F : ℝ × FourSpace → ℝ) (z : ℝ × FourSpace)
    (hF : ContDiffAt ℝ 2 F z) (i j : Fin 4) :
    ContinuousAt (fun w : ℝ × FourSpace =>
      partialDeriv (partialDeriv (fun x => F (w.1, x)) i) j w.2) z := by
  exact fourHeat_slice_partial_continuousAt
    (fun w => partialDeriv (fun x => F (w.1, x)) i w.2) z
    (fourHeat_slice_partial_contDiffAt F z hF i) j

end
end PositiveEinsteinFour.Geometry
end


section

/-! Bounded reconstruction of a compactly supported Euclidean chart
function into the actual base L² space. Null sets are respected by the
proved reverse chart norm comparison. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Function
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance reconstruction_baseProbability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Rellich compactness for the actual scalar H¹ space on the compact
manifold, assembled from the finite smooth partition of unity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

local instance rellichCompactness_frameCompact (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g

local instance rellichCompactness_probability (g : SmoothMetric M) :
    IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

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

theorem heatNormalMetric_row (g : SmoothMetric M) (o : FrameOrientation g)
    (e : FrameBundle g) (v w : FourSpace) (i : Fin 4) :
    (heatNormalMetric g o e v *ᵥ WithLp.ofLp w) i =
      g.inner (frameExponential g o e v)
        (mfderiv I4 I4 (frameExponential g o e) v (coordinateVector i))
        (mfderiv I4 I4 (frameExponential g o e) v w) := by
  let D : FourSpace →L[ℝ] FourSpace := mfderiv I4 I4 (frameExponential g o e) v
  let B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ := g.inner (frameExponential g o e v)
  have hw : w = ∑ j : Fin 4, w j • coordinateVector j := by
    simpa only [WithLp.toLp_ofLp] using (sum_coordinateVector (WithLp.ofLp w)).symm
  change (∑ j : Fin 4, B (D (coordinateVector i)) (D (coordinateVector j)) * w j) =
    B (D (coordinateVector i)) (D w)
  conv_rhs => rw [hw, map_sum]
  simp only [map_smul, map_sum, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
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

theorem fourHeat_normalized_amplitude_radial (J u : FourSpace → ℝ) (x : FourSpace)
    (hJ : DifferentiableAt ℝ J x) (hu : DifferentiableAt ℝ u x)
    (hnorm : ∀ᶠ y in 𝓝 x, u y ^ 2 * J y = 1) :
    fderiv ℝ u x x + (fderiv ℝ J x x / (2 * J x)) * u x = 0 := by
  have hn := hnorm.self_of_nhds
  have hu0 : u x ≠ 0 := by intro h; simp [h] at hn
  have hJ0 : J x ≠ 0 := by intro h; simp [h] at hn
  have hd := (hu.hasFDerivAt.pow 2).mul hJ.hasFDerivAt
  have heq : (fun _ : FourSpace => (1 : ℝ)) =ᶠ[𝓝 x] (fun y => u y ^ 2 * J y) := by
    filter_upwards [hnorm] with y hy
    exact hy.symm
  have hL := (hd.congr_of_eventuallyEq heq).unique
    (hasFDerivAt_const (1 : ℝ) x)
  have hv := congrArg (fun L : FourSpace →L[ℝ] ℝ => L x) hL
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    _root_.zero_apply] at hv
  norm_num [smul_eq_mul] at hv
  have hcancel : u x * (2 * J x * fderiv ℝ u x x + u x * fderiv ℝ J x x) = 0 := by
    nlinarith only [hv]
  have hc := (mul_eq_zero.mp hcancel).resolve_left hu0
  field_simp [hJ0]
  nlinarith only [hc]

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

theorem fourHeatOneZero_gaussian (C : Mat4) (t : ℝ)
    (u : FourSpace → Fin 4 → ℝ) (x : FourSpace) (k : Fin 4) :
    fourHeatOneZero C (fun y l => fourHeatGaussian t y * u y l) x k =
      fourHeatGaussian t x * fourHeatOneZero C u x k := by
  unfold fourHeatOneZero
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthonormal-frame coefficients of the actual H1 completion have
compact Euclidean H1 localizations. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open scoped BigOperators Manifold ContDiff

noncomputable section

local instance instMeasurableSpaceFourSpace_2 : MeasurableSpace FourSpace := borel FourSpace
local instance instBorelSpaceFourSpace_2 : BorelSpace FourSpace := ⟨rfl⟩
local instance instMeasureSpaceFourSpace_2 : MeasureSpace FourSpace := measureSpaceOfInnerProductSpace

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint continuity of the actual coefficient operator applied to a C2 family. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter
open scoped ContDiff BigOperators

noncomputable section

theorem fourHeatOneOperator_joint_continuousAt
    (a : FourSpace → Mat4) (b : FourSpace → Fin 4 → ℝ)
    (B : FourSpace → Fin 4 → Mat4) (C : FourSpace → Mat4)
    (F : ℝ × FourSpace → Fin 4 → ℝ) (z : ℝ × FourSpace)
    (ha : ∀ i j, ContinuousAt (fun x => a x i j) z.2)
    (hb : ∀ i, ContinuousAt (fun x => b x i) z.2)
    (hB : ∀ i k l, ContinuousAt (fun x => B x i k l) z.2)
    (hC : ∀ k l, ContinuousAt (fun x => C x k l) z.2)
    (hF : ∀ k, ContDiffAt ℝ 2 (fun w => F w k) z) (k : Fin 4) :
    ContinuousAt (fun w : ℝ × FourSpace =>
      fourHeatOneOperator (a w.2) (b w.2) (B w.2) (C w.2)
        (fun x => F (w.1, x)) w.2 k) z := by
  have h1 (i : Fin 4) (l : Fin 4) :=
    (fourHeat_slice_partial_contDiffAt (fun w => F w l) z (hF l) i).continuousAt
  have h2 (i j : Fin 4) (l : Fin 4) :=
    fourHeat_slice_second_continuousAt (fun w => F w l) z (hF l) i j
  have hA (i j : Fin 4) : ContinuousAt (fun w : ℝ × FourSpace => a w.2 i j) z :=
    (ha i j).comp continuousAt_snd
  have hbb (i : Fin 4) : ContinuousAt (fun w : ℝ × FourSpace => b w.2 i) z :=
    (hb i).comp continuousAt_snd
  have hBB (i : Fin 4) (l : Fin 4) :
      ContinuousAt (fun w : ℝ × FourSpace => B w.2 i k l) z :=
    (hB i k l).comp continuousAt_snd
  have hCC (l : Fin 4) : ContinuousAt (fun w : ℝ × FourSpace => C w.2 k l) z :=
    (hC k l).comp continuousAt_snd
  have hS : ContinuousAt (fun w : ℝ × FourSpace => ∑ i : Fin 4, ∑ j : Fin 4,
      a w.2 i j * partialDeriv (partialDeriv (fun x => F (w.1, x) k) i) j w.2) z :=
    tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => (hA i j).mul (h2 i j k)))
  have hT : ContinuousAt (fun w : ℝ × FourSpace => ∑ i : Fin 4,
      b w.2 i * partialDeriv (fun x => F (w.1, x) k) i w.2) z :=
    tendsto_finsetSum _ (fun i _ => (hbb i).mul (h1 i k))
  have hU : ContinuousAt (fun w : ℝ × FourSpace => ∑ i : Fin 4, ∑ l : Fin 4,
      B w.2 i k l * partialDeriv (fun x => F (w.1, x) l) i w.2) z :=
    tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun l _ => (hBB i l).mul (h1 i l)))
  have hV : ContinuousAt (fun w : ℝ × FourSpace => ∑ l : Fin 4,
      C w.2 k l * F w l) z :=
    tendsto_finsetSum _ (fun l _ => (hCC l).mul (hF l).continuousAt)
  apply (((hS.neg.add hT).add hU).add hV).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun w => by
    rcases w with ⟨s, x⟩
    simp only [fourHeatOneOperator, fourHeatLocalOperator, fourHeatOneFirst, fourHeatOneZero,
      zero_mul, add_zero, Pi.add_apply, Pi.neg_apply]

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

local instance instCompactSpaceFrameBundle_8 (g : SmoothMetric M) : CompactSpace (FrameBundle g) := actual_compactFrameBundle g

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

theorem heat_radial_connection_axis (A : Fin 4 → FourSpace → HeatMat6)
    (hA : ∀ i k l, ContinuousAt (fun x => A i x k l) 0)
    (h : ∀ᶠ x in 𝓝 (0 : FourSpace), (∑ i : Fin 4, x i • A i x) = 0)
    (i : Fin 4) (k l : Fin 6) :
    (fun t : ℝ => A i (t • coordinateVector i) k l) =ᶠ[𝓝 0] fun _ => 0 := by
  apply heat_radial_axis_zero _ i (hA i k l)
  have hc : ContinuousAt (fun t : ℝ => t • coordinateVector i) 0 :=
    (continuous_id.smul continuous_const).continuousAt
  have hct : Tendsto (fun t : ℝ => t • coordinateVector i) (𝓝 0) (𝓝 (0 : FourSpace)) := by
    simpa only [zero_smul] using hc.tendsto
  have hp : ∀ᶠ t : ℝ in 𝓝 0,
      (∑ j : Fin 4, (t • coordinateVector i) j • A j (t • coordinateVector i)) = 0 := by
    exact hct.eventually h
  filter_upwards [hp] with t ht
  have he := congrArg (fun B : HeatMat6 => B k l) ht
  have hes : (∑ j : Fin 4, (t • coordinateVector i) j * A j (t • coordinateVector i) k l) = 0 := by
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] using he
  simpa [coordinateVector, PiLp.single_apply, PiLp.smul_apply] using hes

theorem heat_radial_connection_center (A : Fin 4 → FourSpace → HeatMat6)
    (hA : ∀ i k l, ContinuousAt (fun x => A i x k l) 0)
    (h : ∀ᶠ x in 𝓝 (0 : FourSpace), (∑ i : Fin 4, x i • A i x) = 0) (i : Fin 4) :
    A i 0 = 0 := by
  ext k l
  change A i 0 k l = 0
  simpa only [zero_smul] using (heat_radial_connection_axis A hA h i k l).self_of_nhds

theorem heat_radial_connection_diagonal (A : Fin 4 → FourSpace → HeatMat6)
    (hA : ∀ i k l, DifferentiableAt ℝ (fun x => A i x k l) 0)
    (h : ∀ᶠ x in 𝓝 (0 : FourSpace), (∑ i : Fin 4, x i • A i x) = 0)
    (i : Fin 4) (k l : Fin 6) : partialDeriv (fun x => A i x k l) i 0 = 0 := by
  have hx := heat_radial_connection_axis A (fun i k l => (hA i k l).continuousAt) h i k l
  have hcurve : HasDerivAt (fun t : ℝ => t • coordinateVector i) (coordinateVector i) 0 := by
    have hc := (ContinuousLinearMap.toSpanSingleton ℝ (coordinateVector i)).hasFDerivAt.comp_hasDerivAt
      0 (hasDerivAt_id (0 : ℝ))
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul, Function.comp_def, id_eq] using! hc
  have hf : HasDerivAt (fun t : ℝ => A i (t • coordinateVector i) k l)
      (partialDeriv (fun x => A i x k l) i 0) 0 := by
    have hf' : HasFDerivAt (fun x => A i x k l) (fderiv ℝ (fun x => A i x k l) 0)
        ((0 : ℝ) • coordinateVector i) := by simpa only [zero_smul] using (hA i k l).hasFDerivAt
    simpa only [partialDeriv] using! hf'.comp_hasDerivAt 0 hcurve
  have hd : deriv (fun t : ℝ => A i (t • coordinateVector i) k l) 0 = 0 := by
    rw [hx.deriv_eq]
    exact deriv_const _ _
  rwa [hf.deriv] at hd

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

theorem fourHeatOneOperator_add (a : Mat4) (b : Fin 4 → ℝ)
    (B : Fin 4 → Mat4) (C : Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (hu : ∀ l, ContDiff ℝ 2 (fun x => u x l))
    (hv : ∀ l, ContDiff ℝ 2 (fun x => v x l)) (x : FourSpace) (k : Fin 4) :
    fourHeatOneOperator a b B C (fun y l => u y l + v y l) x k =
      fourHeatOneOperator a b B C u x k + fourHeatOneOperator a b B C v x k := by
  unfold fourHeatOneOperator fourHeatOneFirst fourHeatOneZero
  rw [fourHeatLocalOperator_add a b 0 _ _ (hu k) (hv k)]
  have hp (i : Fin 4) (l : Fin 4) :
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

local instance heatNormalAmplitudePairing_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

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

theorem heat_partial_sum_four (F : Fin 4 → FourSpace → ℝ) (x : FourSpace)
    (hF : ∀ k, DifferentiableAt ℝ (F k) x) (i : Fin 4) :
    partialDeriv (fun y => ∑ k, F k y) i x = ∑ k, partialDeriv (F k) i x := by
  unfold partialDeriv
  rw [fderiv_fun_sum (u := Finset.univ) (A := F) (fun k _ => hF k), _root_.sum_apply]

theorem heat_partial_second_coordinate (k i j : Fin 4) (x : FourSpace) :
    partialDeriv (partialDeriv (fun y : FourSpace => y k) i) j x = 0 := by
  have he : partialDeriv (fun y : FourSpace => y k) i = fun _ => if i = k then 1 else 0 :=
    funext (heat_partial_coordinate k i)
  rw [he]
  simp only [partialDeriv, fderiv_const_apply, _root_.zero_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The second order remainder needed for the signed Gaussian coefficient. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Filter Asymptotics Set
open scoped _root_.Topology

noncomputable section

theorem fourHeat_quadratic_hasFDerivAt
    (B : FourSpace →L[ℝ] FourSpace →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x) (x : FourSpace) :
    HasFDerivAt (fun y => (1 / 2 : ℝ) * B y y) (B x) x := by
  have h := (B.hasFDerivAt_of_bilinear (hasFDerivAt_id x)
    (hasFDerivAt_id x)).const_mul (1 / 2 : ℝ)
  apply h.congr_fderiv
  ext y
  change (1 / 2 : ℝ) * (B x y + B y x) = B x y
  rw [hB y x]
  ring

theorem fourHeat_second_order_remainder (f : FourSpace → ℝ)
    (hf : ContDiff ℝ 2 f) :
    (fun x => f x - f 0 - fderiv ℝ f 0 x -
      (1 / 2 : ℝ) * fderiv ℝ (fderiv ℝ f) 0 x x)
      =o[𝓝 0] (fun x : FourSpace => ‖x‖ ^ 2) := by
  let B := fderiv ℝ (fderiv ℝ f) 0
  have hB : ∀ x y, B x y = B y x :=
    hf.contDiffAt.isSymmSndFDerivAt (by norm_num)
  let R := fun x => f x - f 0 - fderiv ℝ f 0 x - (1 / 2 : ℝ) * B x x
  let D := fun x => fderiv ℝ f x - fderiv ℝ f 0 - B x
  have hD : D =o[𝓝 0] (fun x : FourSpace => ‖x‖) := by
    have hh := ((hf.fderiv_right (m := 1) (by norm_num)).differentiable
      one_ne_zero 0).hasFDerivAt.isLittleO.norm_right
    simpa only [sub_zero] using hh
  have hR (x : FourSpace) : HasFDerivAt R (D x) x := by
    exact (((hf.differentiable two_ne_zero x).hasFDerivAt.sub_const (f 0)).sub
      (fderiv ℝ f 0).hasFDerivAt).sub (fourHeat_quadratic_hasFDerivAt B hB x)
  have hh := convex_univ.isLittleO_pow_succ (f := R) (f' := D)
    (x₀ := (0 : FourSpace)) (n := 1) (mem_univ 0)
    (fun x _ => (hR x).hasFDerivWithinAt) (by simpa using hD)
  simpa [R, B] using hh


end
end PositiveEinsteinFour.Geometry
end


section

/-! Scalar components of the actual normal-frame covariant derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_twoForm_partial_component (a : FourSpace → TwoFormFour) (x : FourSpace)
    (ha : DifferentiableAt ℝ a x) (i : Fin 4) (k : Fin 6) :
    partialDeriv (fun y => a y k) i x = (fderiv ℝ a x (coordinateVector i)) k := by
  let π : TwoFormFour →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 6 => ℝ) k
  have h := (π.hasFDerivAt.comp x ha.hasFDerivAt).fderiv
  exact congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) h

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem heatNormalTwoFormNabla_component {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (P : FourSpace → CoordinateFrameSpace) (x : FourSpace)
    (hP : ContDiffAt ℝ 1 P x) (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (i : Fin 4) (k : Fin 6) :
    heatNormalTwoFormNabla o c P u i x k =
      fourHeatCovariantDerivative (heatTwoFormConnection g c P)
        (fun y q => heatNormalTwoFormValue o c P u y q) i x k := by
  have ha := (heatNormalTwoFormValue_contDiffAt 1 hu c P x hP hx).differentiableAt one_ne_zero
  have h := congrFun (heatTwoFormConnectionMatrix_action
    (heatNormalFrameConnection g c P i x) (heatNormalTwoFormValue o c P u x)) k
  change (fderiv ℝ (heatNormalTwoFormValue o c P u) x (coordinateVector i)) k +
    twoFormSkewAction (twoFormExtract (heatNormalFrameConnection g c P i x))
      (heatNormalTwoFormValue o c P u x) k = _
  rw [← heat_twoForm_partial_component _ x ha i k]
  change partialDeriv (fun y => heatNormalTwoFormValue o c P u y k) i x + _ =
    partialDeriv (fun y => heatNormalTwoFormValue o c P u y k) i x + _
  exact congrArg (_ + ·) h.symm

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

theorem fourHeat_norm_sqrt_smul_sq (t : ℝ) (ht : 0 ≤ t) (x : FourSpace) :
    ‖Real.sqrt t • x‖ ^ 2 = t * ‖x‖ ^ 2 := by
  rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt ht]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The coefficient operator of the bundle parametrix is the connection
Laplacian expression with the actual normal-frame curvature potential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalConnectionOperator_eq {g : SmoothMetric M} {o : FrameOrientation g}
    {c : M} {e : FrameBundle g} (D : HeatNormalFrameData g o c e)
    (u : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (hA : ∀ i k l, DifferentiableAt ℝ (fun y => heatTwoFormConnection g c D.point i y k l) x)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) (k : Fin 6) :
    fourHeatCovariantOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatTwoFormConnection g c D.point) (heatNormalPotential g c D.point x) u x k =
    fourHeatBundleOperator (heatNormalMetric g o e x)⁻¹ (heatNormalDrift g o e x)
      (heatNormalBundleFirst D x) (heatNormalBundleZero D x) u x k := by
  apply fourHeatCovariantOperator_eq _ _ _ _ u x _ hA hu k
  intro i j
  exact congrFun (congrFun (heatNormalInverse_symm g o e x) i) j |>.symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! The six-component connection is exactly the tensor connection on
alternating two-tensors, including its scalar derivative. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem heat_twoForm_covariant_tensor (C : Fin 4 → FourSpace → Mat4)
    (a : FourSpace → TwoFormFour) (x : FourSpace)
    (ha : DifferentiableAt ℝ a x) (i : Fin 4) (hC : (C i x)ᵀ = -C i x) :
    tensorCovariantDirection C (fun y => twoFormTensor (a y)) i x =
      twoFormTensor (WithLp.toLp 2 (fun k => fourHeatCovariantDerivative
        (fun j y => heatTwoFormConnectionMatrix (C j y)) (fun y k => a y k) i x k)) := by
  have he : WithLp.toLp 2 (fun k => fourHeatCovariantDerivative
      (fun j y => heatTwoFormConnectionMatrix (C j y)) (fun y k => a y k) i x k) =
      fderiv ℝ a x (coordinateVector i) + twoFormSkewAction (twoFormExtract (C i x)) (a x) := by
    ext k
    change partialDeriv (fun y => a y k) i x +
      (heatTwoFormConnectionMatrix (C i x) *ᵥ WithLp.ofLp (a x)) k = _
    rw [heat_twoForm_partial_component a x ha i k, heatTwoFormConnectionMatrix_action]
    rfl
  rw [he]
  change tensorPartial (fun y => twoFormTensor (a y)) i x -
    tensorSlotAction (C i x) (twoFormTensor (a x)) = _
  rw [tensorPartial_twoForm ha, ← twoFormMatrix_extract _ hC,
    tensorSlotAction_twoForm, sub_neg_eq_add]
  exact (twoFormTensorLinear.map_add _ _).symm

theorem heat_fourCovariant_congr (A : Fin 4 → FourSpace → HeatMat6)
    (u v : FourSpace → Fin 6 → ℝ) (x : FourSpace)
    (h : u =ᶠ[𝓝 x] v) (i : Fin 4) (k : Fin 6) :
    fourHeatCovariantDerivative A u i x k = fourHeatCovariantDerivative A v i x k := by
  have he : (fun y => u y k) =ᶠ[𝓝 x] (fun y => v y k) :=
    h.mono fun y hy => congrFun hy k
  have hd : partialDeriv (fun y => u y k) i x = partialDeriv (fun y => v y k) i x :=
    congrArg (fun L : FourSpace →L[ℝ] ℝ => L (coordinateVector i)) he.fderiv_eq
  simp only [fourHeatCovariantDerivative, hd, h.self_of_nhds]

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

def heatNormalOneOperatorAmplitude (E : HeatNormalOneExtension D)
    (a : FourSpace → FourSpace) (x : FourSpace) : FourSpace :=
  WithLp.toLp 2 (fun k => fourHeatOneOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
    (fun y l => a y l) x k)


end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual second transport coefficient at the center, with its
quadratic Weitzenböck contribution to the signed trace isolated. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped BigOperators Manifold ContDiff Matrix.Norms.Elementwise

noncomputable section

def heatMatrixScalarOperator (a : Mat4) (b : Fin 4 → ℝ)
    (A : FourSpace → HeatMat6) (x : FourSpace) : HeatMat6 :=
  fun k l => fourHeatLocalOperator a b 0 (fun y => A y k l) x

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

theorem heatNormal_tensor_first {o : FrameOrientation g} {u : M → TwoFormFour}
    (hu : TwoFormSmooth o u) (c : M) (P : FourSpace → CoordinateFrameSpace)
    (x : FourSpace) (hP : ContDiffAt ℝ 1 P x)
    (hx : (P x).1 ∈ (chartAt FourSpace c).target)
    (hG : ∀ᶠ y in 𝓝 x, (P y).2ᵀ * metricInChart g c (P y).1 * (P y).2 = 1)
    (i : Fin 4) :
    tensorCovariantDirection (heatNormalFrameConnection g c P)
      (fun y => frameTensor (P y).2 (twoFormCoordinates o u c (P y).1)) i x =
      twoFormTensor (heatNormalTwoFormNabla o c P u i x) := by
  rw [heatNormal_covariant_pullback g c P (twoFormCoordinates o u c) x
    (hP.differentiableAt one_ne_zero)
    (fun a => (hu.coordinates_contDiffAt c (P x).1 hx a).differentiableAt (by first | simp | exact_mod_cast le_top))
    hG.self_of_nhds i]
  exact heatNormalTwoFormNabla_tensor hu c P x hP hx hG i

end
end PositiveEinsteinFour.Geometry
end


section

/-! The four-component covector specialization of the compact connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOneCovariantDerivative_scalar
    (A : Fin 4 → FourSpace → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (f : FourSpace → ℝ) (x : FourSpace) (i : Fin 4) (k : Fin 4)
    (hf : DifferentiableAt ℝ f x) (hu : DifferentiableAt ℝ (fun y => u y k) x) :
    fourHeatOneCovariantDerivative A (fun y l => f y * u y l) i x k =
      partialDeriv f i x * u x k + f x * fourHeatOneCovariantDerivative A u i x k := by
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

theorem fourHeatOneCovariantDerivative_sum_four
    (A : Fin 4 → FourSpace → Mat4) (w : Fin 4 → FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (j : Fin 4) (k : Fin 4)
    (hw : ∀ i, DifferentiableAt ℝ (fun y => w i y k) x) :
    fourHeatOneCovariantDerivative A (fun y l => ∑ i, w i y l) j x k =
      ∑ i, fourHeatOneCovariantDerivative A (w i) j x k := by
  have hd : partialDeriv (fun y => ∑ i, w i y k) j x =
      ∑ i, partialDeriv (fun y => w i y k) j x := by
    unfold partialDeriv
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun i y => w i y k) (fun i _ => hw i),
      _root_.sum_apply]
  change partialDeriv (fun y => ∑ i, w i y k) j x +
    (∑ l, A j x k l * ∑ i, w i x l) = _
  rw [hd]
  simp only [fourHeatOneCovariantDerivative, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun l i => A j x k l * w i x l)]

def fourHeatOneCovariantFlux (A : Fin 4 → FourSpace → Mat4)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ)
    (i : Fin 4) (x : FourSpace) (k : Fin 4) : ℝ :=
  ∑ j, (ρ x * a x i j) * fourHeatOneCovariantDerivative A u j x k

theorem fourHeatOneCovariantFlux_derivative
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i j : Fin 4) (k : Fin 4)
    (hA : ∀ l q, DifferentiableAt ℝ (fun y => A l y k q) x)
    (ha : ∀ l, DifferentiableAt ℝ (fun y => a y i l) x)
    (hρ : DifferentiableAt ℝ ρ x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    fourHeatOneCovariantDerivative A (fourHeatOneCovariantFlux A a ρ u i) j x k =
      ∑ l, (partialDeriv (fun y => ρ y * a y i l) j x *
        fourHeatOneCovariantDerivative A u l x k +
        (ρ x * a x i l) * fourHeatOneCovariantDerivative A
          (fourHeatOneCovariantDerivative A u l) j x k) := by
  unfold fourHeatOneCovariantFlux
  rw [fourHeatOneCovariantDerivative_sum_four A _ x j k (fun l =>
    (hρ.mul (ha l)).mul (fourHeatOneCovariantDerivative_differentiable A u x l k (hA l) hu))]
  apply Finset.sum_congr rfl
  intro l _
  exact fourHeatOneCovariantDerivative_scalar A (fourHeatOneCovariantDerivative A u l)
    (fun y => ρ y * a y i l) x j k (hρ.mul (ha l))
    (fourHeatOneCovariantDerivative_differentiable A u x l k (hA l) hu)

theorem fourHeatOneCovariantOperator_divergence
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : Mat4) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (k : Fin 4)
    (hA : ∀ i l, DifferentiableAt ℝ (fun y => A i y k l) x)
    (ha : ∀ i j, DifferentiableAt ℝ (fun y => a y i j) x)
    (hρ : DifferentiableAt ℝ ρ x) (hρ0 : ρ x ≠ 0)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x)
    (hsym : ∀ i j, a x i j = a x j i) :
    ρ x * fourHeatOneCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A V u x k =
      -(∑ i, fourHeatOneCovariantDerivative A (fourHeatOneCovariantFlux A a ρ u i) i x k) +
        ρ x * ∑ l, V k l * u x l := by
  let Q := ∑ i : Fin 4, ∑ j : Fin 4, a x i j *
    fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u i) j x k
  let B := ∑ i : Fin 4, fourHeatDensityDrift a ρ x i *
    fourHeatOneCovariantDerivative A u i x k
  have hb (i : Fin 4) :
      (∑ j, partialDeriv (fun y => ρ y * a y j i) j x) =
        -(ρ x * fourHeatDensityDrift a ρ x i) := by
    have h := fourHeatDensityDrift_weighted a ρ x i hρ hρ0 (fun j => ha j i)
    linarith only [h]
  have hfirst : (∑ i : Fin 4, ∑ j : Fin 4,
      partialDeriv (fun y => ρ y * a y i j) i x * fourHeatOneCovariantDerivative A u j x k) =
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
        fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u j) i x k) =
      ρ x * Q := by
    rw [Finset.sum_comm]
    simp only [Q, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
    ring
  have hflux (i : Fin 4) := fourHeatOneCovariantFlux_derivative A a ρ u x i i k
    hA (ha i) hρ hu
  have hdiv : (∑ i, fourHeatOneCovariantDerivative A (fourHeatOneCovariantFlux A a ρ u i) i x k) =
      ρ x * Q - ρ x * B := by
    simp_rw [hflux, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    ring
  rw [hdiv]
  change ρ x * (-Q + B + ∑ l, V k l * u x l) = _
  ring

theorem fourHeatOneCovariantFlux_contDiffAt
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ)
    (x : FourSpace) (i : Fin 4) (k : Fin 4)
    (hA : ∀ j l, ContDiffAt ℝ 1 (fun y => A j y k l) x)
    (ha : ∀ j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ContDiffAt ℝ 1 ρ x)
    (hu : ∀ l, ContDiffAt ℝ 2 (fun y => u y l) x) :
    ContDiffAt ℝ 1 (fun y => fourHeatOneCovariantFlux A a ρ u i y k) x := by
  apply ContDiffAt.sum
  intro j _
  exact (hρ.mul (ha j)).mul (fourHeatOneCovariantDerivative_contDiffAt A u x j k (hA j) hu)

theorem fourHeatOneCovariantDerivative_support
    (A : Fin 4 → FourSpace → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (i : Fin 4) (k : Fin 4) :
    tsupport (fun x => fourHeatOneCovariantDerivative A u i x k) ⊆
      ⋃ l : Fin 4, tsupport (fun x => u x l) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite fun l => isClosed_tsupport (fun x => u x l))
  intro x hx
  by_contra hn
  have hu (l : Fin 4) : x ∉ tsupport (fun y => u y l) :=
    fun h => hn (mem_iUnion.mpr ⟨l, h⟩)
  have hp : partialDeriv (fun y => u y k) i x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hu k
      (tsupport_fderiv_apply_subset ℝ (coordinateVector i) h))
  have hz (l : Fin 4) : u x l = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => u y l) (hu l)
  apply hx
  simp only [fourHeatOneCovariantDerivative, hp, hz, mul_zero, Finset.sum_const_zero, zero_add]

theorem fourHeatOneCovariantFlux_support
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ) (i : Fin 4) (k : Fin 4) :
    tsupport (fun x => fourHeatOneCovariantFlux A a ρ u i x k) ⊆
      ⋃ l : Fin 4, tsupport (fun x => u x l) := by
  apply closure_minimal _ (isClosed_iUnion_of_finite fun l => isClosed_tsupport (fun x => u x l))
  intro x hx
  by_contra hn
  have hz (j : Fin 4) : fourHeatOneCovariantDerivative A u j x k = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantDerivative A u j y k)
      (fun h => hn (fourHeatOneCovariantDerivative_support A u j k h))
  apply hx
  simp only [fourHeatOneCovariantFlux, hz, mul_zero, Finset.sum_const_zero]

theorem fourHeatOneCovariantFlux_compact
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ)
    (hc : ∀ k, HasCompactSupport (fun x => u x k)) (i : Fin 4) (k : Fin 4) :
    HasCompactSupport (fun x => fourHeatOneCovariantFlux A a ρ u i x k) :=
  (isCompact_iUnion hc).of_isClosed_subset (isClosed_tsupport _)
    (fourHeatOneCovariantFlux_support A a ρ u i k)

theorem fourHeatOne_covariant_divergence_green
    (A : Fin 4 → FourSpace → Mat4) (u : FourSpace → Fin 4 → ℝ)
    (W : Fin 4 → FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hW : ∀ x ∈ U, ∀ i k, ContDiffAt ℝ 1 (fun y => W i y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ i : Fin 4, ∑ k : Fin 4,
      u x k * fourHeatOneCovariantDerivative A (W i) i x k) =
      -(∑ i : Fin 4, ∫ x, ∑ k : Fin 4, fourHeatOneCovariantDerivative A u i x k * W i x k) := by
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      u x k * fourHeatOneCovariantDerivative A (W i) i x k) :=
    fourHeatOneCovariantDerivative_pairing_integrable A u (W i) U i
      (fun k => (hu k).continuous) hc hs (fun x hx k => hW x hx i k)
      (fun x hx k l => hA x hx i k l)
  rw [integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := fourHeatOneCovariantDerivative_green A u (W i) U i hu hc hs
    (fun x hx k => hW x hx i k) (fun x hx k l => hA x hx i k l)
    (fun x hx => hskew x hx i)
  linarith only [h]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Compactly supported tests only require continuity on the normal chart. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped Manifold ContDiff _root_.Topology

noncomputable section

theorem heat_continuous_mul_of_tsupport_subset {χ f : FourSpace → ℝ}
    {U : Set FourSpace} (hχ : Continuous χ) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hs : tsupport χ ⊆ U) :
    Continuous (fun x => χ x * f x) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hχ.continuousAt.mul ((hf x hx).continuousAt (hU.mem_nhds hx))
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    have hx' : x ∉ tsupport χ := fun h => hx (hs h)
    filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hx'] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The four-component covector specialization of the compact connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOne_potential_pairing_integrable
    (u v : FourSpace → Fin 4 → ℝ) (ρ : FourSpace → ℝ)
    (V : FourSpace → Mat4) (U : Set FourSpace)
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

theorem fourHeatOneCovariantOperator_weighted_green
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : FourSpace → Mat4)
    (u v : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
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
    (∫ x, ∑ k, ρ x * u x k * fourHeatOneCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      (∑ i : Fin 4, ∫ x, ∑ k : Fin 4,
        fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k) +
      ∫ x, ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l) := by
  let W := fourHeatOneCovariantFlux A a ρ v
  let B := fun x => ∑ i : Fin 4, ∑ k : Fin 4,
    u x k * fourHeatOneCovariantDerivative A (W i) i x k
  let P := fun x => ∑ k : Fin 4, u x k * (ρ x * ∑ l : Fin 4, V x k l * v x l)
  have hW (x : FourSpace) (hx : x ∈ U) (i : Fin 4) (k : Fin 4) :
      ContDiffAt ℝ 1 (fun y => W i y k) x :=
    fourHeatOneCovariantFlux_contDiffAt A a ρ v x i k (fun j l => hA x hx j k l)
      (ha x hx i) (hρ x hx) (hv x hx)
  have hBi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      u x k * fourHeatOneCovariantDerivative A (W i) i x k) :=
    fourHeatOneCovariantDerivative_pairing_integrable A u (W i) U i
      (fun k => (hu k).continuous) hc hs (fun x hx k => hW x hx i k)
      (fun x hx k l => (hA x hx i k l).continuousAt)
  have hB : Integrable B := integrable_finsetSum _ (fun i _ => hBi i)
  have hP : Integrable P := fourHeatOne_potential_pairing_integrable u v ρ V U
    (fun k => (hu k).continuous) hc hs (fun x hx k => (hv x hx k).continuousAt)
    (fun x hx => (hρ x hx).continuousAt) hV
  have heq : (fun x => ∑ k : Fin 4, ρ x * u x k *
      fourHeatOneCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      fun x => -B x + P x := by
    funext x
    by_cases hx : x ∈ U
    · have hk (k : Fin 4) := fourHeatOneCovariantOperator_divergence A a ρ (V x) v x k
        (fun i l => (hA x hx i k l).differentiableAt one_ne_zero)
        (fun i j => (ha x hx i j).differentiableAt one_ne_zero)
        ((hρ x hx).differentiableAt one_ne_zero) (hρ0 x hx) (hv x hx) (hsym x hx)
      have hm (k : Fin 4) : ρ x * u x k *
          fourHeatOneCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) v x k =
          -(∑ i : Fin 4, u x k * fourHeatOneCovariantDerivative A (W i) i x k) +
            u x k * (ρ x * ∑ l, V x k l * v x l) := by
        calc
          _ = u x k * (ρ x * fourHeatOneCovariantOperator (a x)
              (fourHeatDensityDrift a ρ x) A (V x) v x k) := by ring
          _ = _ := by rw [hk]; simp only [W, mul_add, mul_neg, Finset.mul_sum]
      simp_rw [hm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_comm (f := fun k i => u x k * fourHeatOneCovariantDerivative A (W i) i x k)]
    · have hz (k : Fin 4) : u x k = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => u y k) (fun h => hx (hs k h))
      simp only [B, P, hz, mul_zero, zero_mul, Finset.sum_const_zero, neg_zero, zero_add]
  rw [heq, integral_add (f := fun x => -B x) (g := P) hB.neg hP, integral_neg]
  have hgreen := fourHeatOne_covariant_divergence_green A u W U hu hc hs hW
    (fun x hx i k l => (hA x hx i k l).continuousAt) hskew
  change -(∫ x, B x) + (∫ x, P x) = _
  rw [hgreen, neg_neg]

theorem fourHeatOne_metric_pairing_symm (a : Mat4)
    (ha : ∀ i j, a i j = a j i) (p q : Fin 4 → ℝ) :
    (∑ i, ∑ j, a i j * p i * q j) = ∑ i, ∑ j, a i j * q i * p j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [ha j i]
  ring

theorem fourHeatOne_potential_pairing_symm (V : Mat4)
    (hV : ∀ k l, V k l = V l k) (u v : Fin 4 → ℝ) :
    (∑ k, u k * ∑ l, V k l * v l) = ∑ k, v k * ∑ l, V k l * u l := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [hV l k]
  ring

theorem fourHeatOne_flux_pairing (A : Fin 4 → FourSpace → Mat4)
    (a : FourSpace → Mat4) (ρ : FourSpace → ℝ)
    (u v : FourSpace → Fin 4 → ℝ) (x : FourSpace) :
    (∑ i : Fin 4, ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k) =
      ρ x * ∑ k : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
        a x i j * fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantDerivative A v j x k := by
  unfold fourHeatOneCovariantFlux
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem fourHeatOne_flux_pairing_swap
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u v : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (ha : ∀ x ∈ U, ∀ i j, a x i j = a x j i) (x : FourSpace) :
    (∑ i : Fin 4, ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A v i x k * fourHeatOneCovariantFlux A a ρ u i x k) =
      ∑ i : Fin 4, ∑ k : Fin 4,
        fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k := by
  by_cases hx : x ∈ U
  · rw [fourHeatOne_flux_pairing, fourHeatOne_flux_pairing]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact fourHeatOne_metric_pairing_symm (a x) (ha x hx)
      (fun i => fourHeatOneCovariantDerivative A v i x k)
      (fun i => fourHeatOneCovariantDerivative A u i x k)
  · have hU : (⋃ k, tsupport (fun y => u y k)) ⊆ U := iUnion_subset hs
    have hD (i : Fin 4) (k : Fin 4) : fourHeatOneCovariantDerivative A u i x k = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantDerivative A u i y k)
        (fun h => hx (hU (fourHeatOneCovariantDerivative_support A u i k h)))
    have hW (i : Fin 4) (k : Fin 4) : fourHeatOneCovariantFlux A a ρ u i x k = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantFlux A a ρ u i y k)
        (fun h => hx (hU (fourHeatOneCovariantFlux_support A a ρ u i k h)))
    simp only [hD, hW, zero_mul, mul_zero, Finset.sum_const_zero]

theorem fourHeatOneCovariantFlux_contDiff
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (u : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
    (hu : ∀ k, ContDiff ℝ 2 (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hA : ∀ x ∈ U, ∀ i k l, ContDiffAt ℝ 1 (fun y => A i y k l) x)
    (ha : ∀ x ∈ U, ∀ i j, ContDiffAt ℝ 1 (fun y => a y i j) x)
    (hρ : ∀ x ∈ U, ContDiffAt ℝ 1 ρ x) (i : Fin 4) (k : Fin 4) :
    ContDiff ℝ 1 (fun x => fourHeatOneCovariantFlux A a ρ u i x k) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact fourHeatOneCovariantFlux_contDiffAt A a ρ u x i k (fun j l => hA x hx j k l)
      (ha x hx i) (hρ x hx) (fun l => (hu l).contDiffAt)
  · have hsub : tsupport (fun y => fourHeatOneCovariantFlux A a ρ u i y k) ⊆ U :=
      (fourHeatOneCovariantFlux_support A a ρ u i k).trans (iUnion_subset hs)
    have hn : x ∉ tsupport (fun y => fourHeatOneCovariantFlux A a ρ u i y k) :=
      fun hh => hx (hsub hh)
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hN := (isClosed_tsupport (fun y => fourHeatOneCovariantFlux A a ρ u i y k)).isOpen_compl.mem_nhds hn
    filter_upwards [hN] with y hy
    exact image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantFlux A a ρ u i y k) hy

theorem fourHeatOneCovariantDerivative_left_integrable
    (A : Fin 4 → FourSpace → Mat4) (u v : FourSpace → Fin 4 → ℝ)
    (U : Set FourSpace) (i : Fin 4)
    (hu : ∀ k, ContDiff ℝ 1 (fun x => u x k))
    (hc : ∀ k, HasCompactSupport (fun x => u x k))
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, (A i x)ᵀ = -A i x) :
    Integrable (fun x => ∑ k, fourHeatOneCovariantDerivative A u i x k * v x k) := by
  let F := fun x => ∑ k : Fin 4, u x k * v x k
  have hF : ContDiff ℝ 1 F := fourHeatOne_pairing_contDiff u v U hu hs hv
  have hcF : HasCompactSupport F := fourHeatOne_pairing_compact u v hc
  have hDc : Continuous (partialDeriv F i) :=
    ((hF.fderiv_right (m := 0) (by norm_num)).clm_apply contDiff_const).continuous
  have hD : Integrable (partialDeriv F i) :=
    hDc.integrable_of_hasCompactSupport
        (hcF.of_isClosed_subset (isClosed_tsupport _)
          (tsupport_fderiv_apply_subset ℝ (coordinateVector i)))
  have hR := fourHeatOneCovariantDerivative_pairing_integrable A u v U i
    (fun k => (hu k).continuous) hc hs hv hA
  apply (hD.sub hR).congr
  filter_upwards [] with x
  have hp := fourHeatOneCovariantDerivative_pairing_global A u v U i hu hs hv hskew x
  change partialDeriv F i x - _ = _
  change partialDeriv F i x = _ at hp
  linarith only [hp]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The four-component covector specialization of the compact connection Green identity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

theorem fourHeatOne_compact_flux_green
    (A : Fin 4 → FourSpace → Mat4)
    (W : Fin 4 → FourSpace → Fin 4 → ℝ) (v : FourSpace → Fin 4 → ℝ)
    (U : Set FourSpace)
    (hW : ∀ i k, ContDiff ℝ 1 (fun x => W i x k))
    (hcW : ∀ i k, HasCompactSupport (fun x => W i x k))
    (hsW : ∀ i k, tsupport (fun x => W i x k) ⊆ U)
    (hv : ∀ x ∈ U, ∀ k, ContDiffAt ℝ 1 (fun y => v y k) x)
    (hA : ∀ x ∈ U, ∀ i k l, ContinuousAt (fun y => A i y k l) x)
    (hskew : ∀ x ∈ U, ∀ i, (A i x)ᵀ = -A i x) :
    (∫ x, ∑ i : Fin 4, ∑ k : Fin 4,
      v x k * fourHeatOneCovariantDerivative A (W i) i x k) =
      -(∑ i : Fin 4, ∫ x, ∑ k : Fin 4,
        fourHeatOneCovariantDerivative A v i x k * W i x k) := by
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      v x k * fourHeatOneCovariantDerivative A (W i) i x k) := by
    simpa only [mul_comm] using fourHeatOneCovariantDerivative_left_integrable A (W i) v U i
      (hW i) (hcW i) (hsW i) hv (fun x hx k l => hA x hx i k l)
      (fun x hx => hskew x hx i)
  rw [integral_finsetSum _ (fun i _ => hi i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := fourHeatOneCovariantDerivative_green A (W i) v U i (hW i) (hcW i) (hsW i)
    hv (fun x hx k l => hA x hx i k l) (fun x hx => hskew x hx i)
  simpa only [mul_comm] using h

theorem fourHeatOne_potential_pairing_swap
    (u v : FourSpace → Fin 4 → ℝ) (ρ : FourSpace → ℝ)
    (V : FourSpace → Mat4) (U : Set FourSpace)
    (hs : ∀ k, tsupport (fun x => u x k) ⊆ U)
    (hV : ∀ x ∈ U, ∀ k l, V x k l = V x l k) (x : FourSpace) :
    (∑ k, v x k * (ρ x * ∑ l, V x k l * u x l)) =
      ∑ k, u x k * (ρ x * ∑ l, V x k l * v x l) := by
  by_cases hx : x ∈ U
  · have hp (p q : Fin 4 → ℝ) : (∑ k, p k * (ρ x * ∑ l, V x k l * q l)) =
        ρ x * ∑ k, p k * ∑ l, V x k l * q l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hp, hp, fourHeatOne_potential_pairing_symm (V x) (hV x hx)]
  · have hz (k : Fin 4) : u x k = 0 := image_eq_zero_of_notMem_tsupport
      (f := fun y => u y k) (fun h => hx (hs k h))
    simp only [hz, mul_zero, Finset.sum_const_zero, zero_mul]

theorem fourHeatOneCovariantOperator_compact_adjoint
    (A : Fin 4 → FourSpace → Mat4) (a : FourSpace → Mat4)
    (ρ : FourSpace → ℝ) (V : FourSpace → Mat4)
    (u v : FourSpace → Fin 4 → ℝ) (U : Set FourSpace)
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
    (∫ x, ∑ k, ρ x * u x k * fourHeatOneCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) v x k) =
      ∫ x, ∑ k, ρ x * v x k * fourHeatOneCovariantOperator (a x)
        (fourHeatDensityDrift a ρ x) A (V x) u x k := by
  let W := fourHeatOneCovariantFlux A a ρ u
  let B := fun x => ∑ i : Fin 4, ∑ k : Fin 4,
    v x k * fourHeatOneCovariantDerivative A (W i) i x k
  let P := fun x => ∑ k : Fin 4, u x k * (ρ x * ∑ l : Fin 4, V x k l * v x l)
  have hW (i : Fin 4) (k : Fin 4) : ContDiff ℝ 1 (fun x => W i x k) :=
    fourHeatOneCovariantFlux_contDiff A a ρ u U hu hs hA ha hρ i k
  have hcW (i : Fin 4) (k : Fin 4) : HasCompactSupport (fun x => W i x k) :=
    fourHeatOneCovariantFlux_compact A a ρ u hc i k
  have hsW (i : Fin 4) (k : Fin 4) : tsupport (fun x => W i x k) ⊆ U :=
    (fourHeatOneCovariantFlux_support A a ρ u i k).trans (iUnion_subset hs)
  have hBi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      v x k * fourHeatOneCovariantDerivative A (W i) i x k) := by
    simpa only [mul_comm] using fourHeatOneCovariantDerivative_left_integrable A (W i) v U i
      (hW i) (hcW i) (hsW i) (fun x hx k => (hv x hx k).of_le (by norm_num))
      (fun x hx k l => (hA x hx i k l).continuousAt) (fun x hx => hskew x hx i)
  have hB : Integrable B := integrable_finsetSum _ (fun i _ => hBi i)
  have hP : Integrable P := fourHeatOne_potential_pairing_integrable u v ρ V U
    (fun k => (hu k).continuous) hc hs (fun x hx k => (hv x hx k).continuousAt)
    (fun x hx => (hρ x hx).continuousAt) hV
  have heq : (fun x => ∑ k : Fin 4, ρ x * v x k *
      fourHeatOneCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) u x k) =
      fun x => -B x + P x := by
    funext x
    by_cases hx : x ∈ U
    · have hk (k : Fin 4) := fourHeatOneCovariantOperator_divergence A a ρ (V x) u x k
        (fun i l => (hA x hx i k l).differentiableAt one_ne_zero)
        (fun i j => (ha x hx i j).differentiableAt one_ne_zero)
        ((hρ x hx).differentiableAt one_ne_zero) (hρ0 x hx)
        (fun l => (hu l).contDiffAt) (hsym x hx)
      have hm (k : Fin 4) : ρ x * v x k *
          fourHeatOneCovariantOperator (a x) (fourHeatDensityDrift a ρ x) A (V x) u x k =
          -(∑ i : Fin 4, v x k * fourHeatOneCovariantDerivative A (W i) i x k) +
            v x k * (ρ x * ∑ l, V x k l * u x l) := by
        calc
          _ = v x k * (ρ x * fourHeatOneCovariantOperator (a x)
              (fourHeatDensityDrift a ρ x) A (V x) u x k) := by ring
          _ = _ := by rw [hk]; simp only [W, mul_add, mul_neg, Finset.mul_sum]
      simp_rw [hm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [Finset.sum_comm (f := fun k i => v x k * fourHeatOneCovariantDerivative A (W i) i x k),
        fourHeatOne_potential_pairing_swap u v ρ V U hs hVsym x]
    · have hz (k : Fin 4) : u x k = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun y => u y k) (fun h => hx (hs k h))
      have hD (i : Fin 4) (k : Fin 4) : fourHeatOneCovariantDerivative A u i x k = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantDerivative A u i y k)
          (fun h => hx ((iUnion_subset hs) (fourHeatOneCovariantDerivative_support A u i k h)))
      have hDD (i j : Fin 4) (k : Fin 4) :
          fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u i) j x k = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun y =>
          fourHeatOneCovariantDerivative A (fourHeatOneCovariantDerivative A u i) j y k)
        intro h
        obtain ⟨l, hl⟩ := mem_iUnion.mp (fourHeatOneCovariantDerivative_support A
          (fourHeatOneCovariantDerivative A u i) j k h)
        exact hx ((iUnion_subset hs) (fourHeatOneCovariantDerivative_support A u i l hl))
      have hDW (i : Fin 4) (k : Fin 4) : fourHeatOneCovariantDerivative A (W i) i x k = 0 := by
        apply image_eq_zero_of_notMem_tsupport (f := fun y => fourHeatOneCovariantDerivative A (W i) i y k)
        intro h
        exact hx ((iUnion_subset (hsW i)) (fourHeatOneCovariantDerivative_support A (W i) i k h))
      simp only [B, P, fourHeatOneCovariantOperator, hz, hD, hDD, hDW,
        zero_mul, mul_zero, Finset.sum_const_zero, neg_zero, add_zero]
  have hgreen := fourHeatOne_compact_flux_green A W v U hW hcW hsW
    (fun x hx k => (hv x hx k).of_le (by norm_num))
    (fun x hx i k l => (hA x hx i k l).continuousAt) hskew
  have hi (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A v i x k * W i x k) := by
    simpa only [mul_comm] using fourHeatOneCovariantDerivative_pairing_integrable A (W i) v U i
      (fun k => (hW i k).continuous) (hcW i) (hsW i)
      (fun x hx k => (hv x hx k).of_le (by norm_num))
      (fun x hx k l => (hA x hx i k l).continuousAt)
  have hj (i : Fin 4) : Integrable (fun x => ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k) :=
    fourHeatOneCovariantDerivative_left_integrable A u (fourHeatOneCovariantFlux A a ρ v i) U i
      (fun k => (hu k).of_le (by norm_num)) hc hs
      (fun x hx k => fourHeatOneCovariantFlux_contDiffAt A a ρ v x i k
        (fun j l => hA x hx j k l) (ha x hx i) (hρ x hx) (hv x hx))
      (fun x hx k l => (hA x hx i k l).continuousAt) (fun x hx => hskew x hx i)
  have hflux : (∑ i : Fin 4, ∫ x, ∑ k : Fin 4,
      fourHeatOneCovariantDerivative A v i x k * W i x k) =
      ∑ i : Fin 4, ∫ x, ∑ k : Fin 4,
        fourHeatOneCovariantDerivative A u i x k * fourHeatOneCovariantFlux A a ρ v i x k := by
    rw [← integral_finsetSum _ (fun i _ => hi i), ← integral_finsetSum _ (fun i _ => hj i)]
    apply integral_congr_ae
    filter_upwards [] with x
    exact fourHeatOne_flux_pairing_swap A a ρ u v U hs hsym x
  rw [heq, integral_add (f := fun x => -B x) (g := P) hB.neg hP, integral_neg]
  change _ = -(∫ x, B x) + (∫ x, P x)
  rw [hgreen, neg_neg, hflux]
  exact fourHeatOneCovariantOperator_weighted_green A a ρ V u v U
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

/-! Pairing compact normal one-form amplitudes with actual smooth sections. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heat_oneTensor_inner (T U : CovariantCoordinates 1) :
    inner ℝ (WithLp.toLp 2 (fun i => T ![i]) : FourSpace) (WithLp.toLp 2 (fun i => U ![i])) =
      frameTensorPairing T U := by
  unfold frameTensorPairing
  rw [sum_tensor_indices_cons]
  simp only [Fintype.sum_unique, PiLp.inner_apply, Real.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply congrArg₂ (· * ·)
  · apply congrArg T
    ext j
    fin_cases j
    rfl
  · apply congrArg U
    ext j
    fin_cases j
    rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}

def heatNormalOneValue (c : M) (P : FourSpace → CoordinateFrameSpace)
    (v : smoothCovariantFields M 1) (x : FourSpace) : FourSpace :=
  WithLp.toLp 2 (heatNormalOneFormValue c P v x)

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

local instance heatNormalOneAmplitudePairing_probability : IsProbabilityMeasure (normalizedVolume g) :=
  normalizedVolume_isProbability (actual_finitePositiveVolume g)

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

def heatNormalOperatorAmplitude (E : HeatNormalBundleExtension D)
    (a : FourSpace → TwoFormFour) (x : FourSpace) : TwoFormFour :=
  WithLp.toLp 2 (fun k => fourHeatBundleOperator (E.base.a x) (E.base.b x) (E.B x) (E.C x)
    (fun y l => a y l) x k)

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

theorem heatAmplitude_component_support (a : FourSpace → TwoFormFour) (k : Fin 6) :
    tsupport (fun x => a x k) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  contrapose! hx
  apply Function.notMem_support.mpr
  rw [Function.notMem_support.mp hx]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Joint positive-time regularity of the actual cutoff normal kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set
open scoped ContDiff Manifold _root_.Topology

noncomputable section

theorem fourHeatPolynomial_joint_contDiff (u : Fin 4 → FourSpace → ℝ)
    (hu : ∀ m, ContDiff ℝ 2 (u m)) :
    ContDiff ℝ 2 (fun z : ℝ × FourSpace => fourHeatPolynomial u z.1 z.2) := by
  have h (m : Fin 4) : ContDiff ℝ 2 (fun z : ℝ × FourSpace => u m z.2) :=
    (hu m).comp contDiff_snd
  exact (((h 0).add (contDiff_fst.mul (h 1))).add
    ((contDiff_fst.pow 2).mul (h 2))).add ((contDiff_fst.pow 3).mul (h 3))

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

theorem heat_weighted_inner_sum (ρ : ℝ) (u v : TwoFormFour) :
    ρ * inner ℝ u v = ∑ k : Fin 6, ρ * u k * v k := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual compact one-form amplitudes satisfy the geometric Green identity. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter Metric MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section

theorem heatOneAmplitude_component_support (a : FourSpace → FourSpace) (k : Fin 4) :
    tsupport (fun x => a x k) ⊆ tsupport a := by
  apply closure_mono
  intro x hx
  contrapose! hx
  apply Function.notMem_support.mpr
  rw [Function.notMem_support.mp hx]
  rfl


end

section

theorem heat_one_weighted_inner_sum (ρ : ℝ) (u v : FourSpace) :
    ρ * inner ℝ u v = ∑ k : Fin 4, ρ * u k * v k := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring


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

def heatOneMatrixScalarOperator (a : Mat4) (b : Fin 4 → ℝ)
    (A : FourSpace → Mat4) (x : FourSpace) : Mat4 :=
  fun k l => fourHeatLocalOperator a b 0 (fun y => A y k l) x

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual signed normal-parametrix Gaussian integral has the
signature curvature density as its limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators ContDiff Manifold _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

def heatNormalMatrixPolynomial (E : HeatNormalBundleExtension D)
    (t : ℝ) (x : FourSpace) : HeatMat6 :=
  E.amplitude 0 x + t • E.amplitude 1 x + t ^ 2 • E.amplitude 2 x + t ^ 3 • E.amplitude 3 x

theorem heatNormalMatrixPolynomial_component (E : HeatNormalBundleExtension D)
    (t : ℝ) (x : FourSpace) (k l : Fin 6) :
    heatNormalMatrixPolynomial E t x k l =
      fourHeatPolynomial (fun m y => E.amplitude m y k l) t x := by
  simp only [heatNormalMatrixPolynomial, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, fourHeatPolynomial]
  norm_num

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


