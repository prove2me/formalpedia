-- Prove2me | Definitions.Def_OAIQ091C044
-- name    : OAIQ091C044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T18:37:21.449487+00:00
-- url     : https://prove2.me/theorems/4f30034a-0bc1-4e65-b077-61f9e64bd965
-- title:
--   Definitions bundle OAIQ091C044 of the split of OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 179 declarations of OpenAI's Lean: 44 definitions, 4 instances and 131 theorems. The definitions and types are `OAI.PositiveEinsteinFour.Geometry.OneFormCoexactEigenIndex`, `OAI.PositiveEinsteinFour.Geometry.OneFormCoexactSpectralSpace`, `OAI.PositiveEinsteinFour.Geometry.OneFormEigenIndex`, `OAI.PositiveEinsteinFour.Geometry.TwoFormSmoothEigenSpace`, `OAI.PositiveEinsteinFour.Geometry.oneFormCodiffEigenMap`, `OAI.PositiveEinsteinFour.Geometry.oneFormCoexactEigenvector`, `OAI.PositiveEinsteinFour.Geometry.oneFormDerivedFamily`, `OAI.PositiveEinsteinFour.Geometry.oneFormEigenSection`, `OAI.PositiveEinsteinFour.Geometry.oneFormEigenvector`, `OAI.PositiveEinsteinFour.Geometry.oneFormExactEigenvector`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatRate`, `OAI.PositiveEinsteinFour.Geometry.oneFormHeatWeight`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenbasis`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenfunction`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenvector`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseHeat`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseHeatPowerSource`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralEquiv`, `OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralMultiplier`, `OAI.PositiveEinsteinFour.Geometry.scalarChartValue`, `OAI.PositiveEinsteinFour.Geometry.scalarChartValueLin`, `OAI.PositiveEinsteinFour.Geometry.scalarH1BaseL4`, `OAI.PositiveEinsteinFour.Geometry.scalarH1BorelCutoffJet`, `OAI.PositiveEinsteinFour.Geometry.scalarH1ChartDerivative`, `OAI.PositiveEinsteinFour.Geometry.scalarH1ChartValue`, `OAI.PositiveEinsteinFour.Geometry.scalarH1CutoffDerivative`, `OAI.PositiveEinsteinFour.Geometry.scalarH1CutoffEuclideanH1`, `OAI.PositiveEinsteinFour.Geometry.scalarH1CutoffGradientL2`, `OAI.PositiveEinsteinFour.Geometry.scalarH1CutoffSupportedH1`, `OAI.PositiveEinsteinFour.Geometry.scalarH1CutoffValueL2`, `OAI.PositiveEinsteinFour.Geometry.scalarH1ReconstructedPiece`, `OAI.PositiveEinsteinFour.Geometry.scalarHeatConvolution`, `OAI.PositiveEinsteinFour.Geometry.scalarWeightedChartL2`, `OAI.PositiveEinsteinFour.Geometry.smoothHodgeLaplacianLinear`, `OAI.PositiveEinsteinFour.Geometry.smoothScalarChartDerivative`, `OAI.PositiveEinsteinFour.Geometry.twoFormEigenform`, `OAI.PositiveEinsteinFour.Geometry.twoFormHarmonicProjection`, `OAI.PositiveEinsteinFour.Geometry.twoFormPotentialKernelValue`, `OAI.PositiveEinsteinFour.Geometry.twoFormPotentialResolvent`, `OAI.PositiveEinsteinFour.Geometry.twoFormRegularizedHodge` and 4 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`EinsteinFour_GeodesicGeometry04`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry04.lean), [`EinsteinFour_GeodesicGeometry05`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry05.lean), [`EinsteinFour_GeodesicGeometry06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeodesicGeometry06.lean), [`EinsteinFour_HeatKernels10`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HeatKernels10.lean), [`EinsteinFour_HodgeTheory08`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory08.lean), [`EinsteinFour_HodgeTheory09`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory09.lean), [`EinsteinFour_HodgeTheory11`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HodgeTheory11.lean), [`EinsteinFour_ScalarRegularity06`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity06.lean), [`EinsteinFour_ScalarRegularity07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/ScalarRegularity07.lean), [`EinsteinFour_WeylEstimates03`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates03.lean), [`EinsteinFour_WeylEstimates07`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates07.lean).
--
--   **Imports.** It imports the published bundle `Def_EinsteinFour`; the bundles `OAIQ091C043` and `OAIQ091C027` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ091C030`, `OAIQ091C031`, `OAIQ091C058`, `OAIQ091C059`, `OAIQ091C060`, `OAIQ091C062`, `OAIQ091C064` and `OAIQ091C068`; the proofs of `OAI_PositiveEinsteinFour_Geometry_ScalarCovariantData_curvature_identity` and `OAI_PositiveEinsteinFour_Geometry_smooth_weighted_variance_ae`.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 7ef5c0c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C043
import Definitions.Def_OAIQ091C027

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


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

theorem twoFormH1ToL2_norm_le (u : TwoFormH1 o) : ‖twoFormH1ToL2 u‖ ≤ ‖u‖ := by
  refine UniformSpace.Completion.induction_on u
    (isClosed_le (continuous_norm.comp twoFormH1ToL2.continuous) continuous_norm) ?_
  intro v
  change ‖twoFormH1ToL2 (smoothTwoFormToH1 v)‖ ≤ ‖smoothTwoFormToH1 v‖
  rw [twoFormH1ToL2_smooth, smoothTwoFormToL2.norm_map, smoothTwoFormToH1.norm_map]
  exact smoothH1ToL2Linear_norm_le v

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Jacobi.matrixContinuousENorm_p2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual exponential differential and its metric Jacobian. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix Filter Set
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_metric_jacobian (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (d : M)
    (e : FrameBundle g) (he : e ∈ o.positive) (t : ℝ) (ht : 0 < t)
    (hd : (parallelFrameFlowMap g 0 t e).base ∈ (chartAt FourSpace d).source) :
    chartVolumeDensity g d (chartAt FourSpace d (parallelFrameFlowMap g 0 t e).base) *
      |LinearMap.det (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
        (frameExponential g o e v)) (t • coordinateVector 0)).toLinearMap| =
        |((actualJacobiSolution g hRic e).J t).det / t ^ 3| := by
  rw [(frameExponential_hasFDerivAt g o hRic d e he t ht hd).fderiv]
  exact jacobiBlockMatrix_scaled_linear_density g d (parallelFrameFlowMap g 0 t e) hd
    t ((actualJacobiSolution g hRic e).J t)

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

theorem frameExponential_radial_norm (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (q : Directions) (t : ℝ) (ht : 0 < t) :
    metricTangentNorm g (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) q.val) = 1 := by
  rw [metricTangentNorm_eq_sqrt, frameExponential_gauss g o hRic e he q t ht q.val,
    real_inner_self_eq_norm_sq, q.property, one_pow, Real.sqrt_one]

theorem frameExponential_radial_pairing_le (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (q : Directions) (t : ℝ) (ht : 0 < t) (w : FourSpace) :
    |⟪q.val, w⟫_ℝ| ≤ metricTangentNorm g (frameExponential g o e (t • q.val))
      (mfderiv I4 I4 (frameExponential g o e) (t • q.val) w) := by
  have h := metric_inner_abs_le g (frameExponential g o e (t • q.val))
    (mfderiv I4 I4 (frameExponential g o e) (t • q.val) q.val)
    (mfderiv I4 I4 (frameExponential g o e) (t • q.val) w)
  rw [frameExponential_gauss g o hRic e he q t ht w,
    frameExponential_radial_norm g o hRic e he q t ht, one_mul] at h
  exact h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth approximations to radial distance have differential bounded by
the actual metric speed after applying the exponential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular
open scoped Manifold ContDiff _root_.Topology InnerProductSpace

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem smoothRadialNorm_exponential_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (ε : ℝ) (hε : 0 < ε) (v w : FourSpace) :
    |fderiv ℝ (smoothRadialNorm ε) v w| ≤
      metricTangentNorm g (frameExponential g o e v)
        (mfderiv I4 I4 (frameExponential g o e) v w) := by
  rw [(smoothRadialNorm_hasFDerivAt ε hε v).fderiv]
  change |(smoothRadialNorm ε v)⁻¹ * ⟪v, w⟫_ℝ| ≤ _
  by_cases hv : v = 0
  · subst v
    simp only [inner_zero_left, mul_zero, abs_zero]
    rw [metricTangentNorm_eq_sqrt]
    exact Real.sqrt_nonneg _
  · let q : Directions := ⟨‖v‖⁻¹ • v, by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
    have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hvq : ‖v‖ • q.val = v := by
      change ‖v‖ • (‖v‖⁻¹ • v) = v
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hpair := frameExponential_radial_pairing_le g o hRic e he q ‖v‖ hr w
    rw [hvq] at hpair
    have hinner : ⟪v, w⟫_ℝ = ‖v‖ * ⟪q.val, w⟫_ℝ := by
      calc
        _ = ⟪‖v‖ • q.val, w⟫_ℝ := congrArg (fun z => ⟪z, w⟫_ℝ) hvq.symm
        _ = _ := real_inner_smul_left _ _ _
    have hfac : (smoothRadialNorm ε v)⁻¹ * ‖v‖ ≤ 1 := by
      rw [← div_eq_inv_mul]
      exact (div_le_one (smoothRadialNorm_pos ε hε v)).mpr
        (smoothRadialNorm_bounds ε hε v).1
    rw [hinner, ← mul_assoc, abs_mul,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (smoothRadialNorm_pos ε hε v).le)
        (norm_nonneg v))]
    exact (mul_le_of_le_one_left (abs_nonneg _) hfac).trans hpair

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

/-! Gauss' lemma integrated along a C1 interval path. The nonnegative
integral formulation agrees with the definition of Riemannian path length. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Set MeasureTheory
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_radial_le_lintegral (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (α : ℝ → FourSpace) (a b : ℝ) (hab : a ≤ b)
    (hα : ContDiffOn ℝ 1 α (Icc a b)) (hstart : α a = 0) :
    ENNReal.ofReal ‖α b‖ ≤ ∫⁻ t in Icc a b,
      metricTangentENorm g (frameExponential g o e (α t))
        (mfderiv I4 I4 (frameExponential g o e) (α t) (derivWithin α (Icc a b) t)) := by
  rcases hab.eq_or_lt with hab | hab
  · subst b
    simp only [hstart, norm_zero, ENNReal.ofReal_zero, zero_le]
  let B := ∫⁻ t in Icc a b,
    metricTangentENorm g (frameExponential g o e (α t))
      (mfderiv I4 I4 (frameExponential g o e) (α t) (derivWithin α (Icc a b) t))
  by_cases hB : B = (⊤ : ℝ≥0∞)
  · change ENNReal.ofReal ‖α b‖ ≤ B
    rw [hB]
    exact le_top
  have hreal : ‖α b‖ ≤ B.toReal := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let F := fun t => smoothRadialNorm ε (α t)
    have hR : ContDiff ℝ 1 (smoothRadialNorm ε) :=
      ((contDiff_norm_sq ℝ).add contDiff_const).sqrt (fun v => by
        have hp : 0 < ‖v‖ ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg ‖v‖]
        exact hp.ne')
    have hF : ContDiffOn ℝ 1 F (Icc a b) := hR.comp_contDiffOn hα
    have hd (t : ℝ) (ht : t ∈ Icc a b) : derivWithin F (Icc a b) t =
        fderiv ℝ (smoothRadialNorm ε) (α t) (derivWithin α (Icc a b) t) := by
      have hu := uniqueDiffOn_Icc hab t ht
      have h := (smoothRadialNorm_hasFDerivAt ε hε (α t)).comp_hasDerivWithinAt t
        ((hα.differentiableOn one_ne_zero t ht).hasDerivWithinAt)
      change derivWithin (smoothRadialNorm ε ∘ α) (Icc a b) t = _
      rw [h.derivWithin hu, (smoothRadialNorm_hasFDerivAt ε hε (α t)).fderiv]
    have hb : ∫⁻ t in Icc a b, ‖derivWithin F (Icc a b) t‖ₑ ≤ B := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [hd t ht, metricTangentENorm_eq_ofReal, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.norm_eq_abs]
      exact smoothRadialNorm_exponential_bound g o hRic e he ε hε (α t)
        (derivWithin α (Icc a b) t)
    have hi := (enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hF hab.le).trans hb
    have hr : F b - F a ≤ B.toReal := by
      apply le_trans (le_abs_self _)
      apply (ENNReal.ofReal_le_iff_le_toReal hB).mp
      simpa only [Real.enorm_eq_ofReal_abs] using hi
    have ha : F a = ε := by
      simp [F, smoothRadialNorm, hstart, Real.sqrt_sq_eq_abs, abs_of_pos hε]
    have hb' : ‖α b‖ ≤ F b := (smoothRadialNorm_bounds ε hε (α b)).1
    linarith
  exact (ENNReal.ofReal_le_iff_le_toReal hB).mpr hreal

theorem frameExponential_inverse_path_length (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hzero : 0 ∈ C.source) (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target)
    (γ : ℝ → M) (a b : ℝ) (hab : a < b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 γ (Icc a b))
    (himage : MapsTo γ (Icc a b) C.target) (hstart : γ a = e.base) :
    ENNReal.ofReal ‖C.symm (γ b)‖ ≤
      (let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩;
        Manifold.pathELength I4 γ a b) := by
  let α := C.symm ∘ γ
  have hαm : ContMDiffOn 𝓘(ℝ, ℝ) I4 1 α (Icc a b) := hI.comp hγ himage
  have hα : ContDiffOn ℝ 1 α (Icc a b) := hαm.contDiffOn
  have hCzero : C 0 = e.base := (hC hzero).trans (frameExponential_zero g o e)
  have hαzero : α a = 0 := by
    change C.symm (γ a) = 0
    rw [hstart, ← hCzero]
    exact C.left_inv hzero
  have hEq : EqOn (fun t => frameExponential g o e (α t)) γ (Icc a b) := by
    intro t ht
    have hv := C.map_target (himage ht)
    exact (hC hv).symm.trans (C.right_inv (himage ht))
  have hs := frameExponential_radial_le_lintegral g o hRic e he α a b hab.le hα hαzero
  apply hs.trans_eq
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  have hu : UniqueMDiffWithinAt 𝓘(ℝ, ℝ) (Icc a b) t := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact uniqueDiffOn_Icc hab t ht
  have hcomp := mfderiv_comp_mfderivWithin t
    ((frameExponential_contMDiff g o e).mdifferentiable one_ne_zero (α t))
    (hαm.mdifferentiableOn one_ne_zero t ht) hu
  have hD : mfderivWithin 𝓘(ℝ, ℝ) I4
      (fun s => frameExponential g o e (α s)) (Icc a b) t 1 =
      mfderiv I4 I4 (frameExponential g o e) (α t) (derivWithin α (Icc a b) t) := by
    have ha : mfderivWithin 𝓘(ℝ, ℝ) I4 α (Icc a b) t 1 =
        derivWithin α (Icc a b) t := by
      have hf : (fderivWithin ℝ α (Icc a b) t) (1 : ℝ) =
          derivWithin α (Icc a b) t := fderivWithin_derivWithin
      simpa only [mfderivWithin_eq_fderivWithin] using! hf
    have hc := congrArg (fun L : ℝ →L[ℝ]
      TangentSpace I4 (frameExponential g o e (α t)) => L 1) hcomp
    exact hc.trans (congrArg (mfderiv I4 I4 (frameExponential g o e) (α t)) ha)
  have hspeed := congrArg
    (fun p : TangentBundle I4 M => metricTangentENorm g p.1 p.2)
    (tangentMapWithin_congr hEq (⟨t, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ) ht)
  change metricTangentENorm g (frameExponential g o e (α t))
      (mfderivWithin 𝓘(ℝ, ℝ) I4 (fun s => frameExponential g o e (α s)) (Icc a b) t 1) =
    metricTangentENorm g (γ t) (mfderivWithin 𝓘(ℝ, ℝ) I4 γ (Icc a b) t 1) at hspeed
  exact (congrArg (metricTangentENorm g (frameExponential g o e (α t))) hD).symm.trans
    hspeed

end
end PositiveEinsteinFour.Geometry
end


section

/-! Short paths cannot leave a normal-coordinate ball. This supplies the
distance lower bound needed for locally minimizing radial geodesics. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle Filter Set MeasureTheory Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_short_path_stays (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target) (r : ℝ) (hr : 0 < r)
    (hball : closedBall 0 r ⊆ C.source)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I4 1 γ) (hstart : γ 0 = e.base)
    (hlen : (let : RiemannianBundle (TangentSpace I4 : M → Type _) :=
      ⟨g.toRiemannianMetric⟩; Manifold.pathELength I4 γ 0 1) < ENNReal.ofReal r) :
    MapsTo γ (Icc 0 1) (C '' closedBall 0 r) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  let K := C '' closedBall 0 r
  let U := C '' ball 0 r
  have hzero : (0 : FourSpace) ∈ C.source := hball (mem_closedBall_self hr.le)
  have hCzero : C 0 = e.base := (hC hzero).trans (frameExponential_zero g o e)
  have hKclosed : IsClosed K :=
    ((isCompact_closedBall (0 : FourSpace) r).image_of_continuousOn
      (C.continuousOn.mono hball)).isClosed
  have hUopen : IsOpen U := C.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hball)
  have hUK : U ⊆ K := image_mono ball_subset_closedBall
  have hKtarget : K ⊆ C.target := by
    rintro y ⟨v, hv, rfl⟩
    exact C.map_source (hball hv)
  let A := γ ⁻¹' K
  have hAclosed : IsClosed (A ∩ Icc 0 1) :=
    (hKclosed.preimage hγ.continuous).inter isClosed_Icc
  have hA0 : 0 ∈ A := by
    change γ 0 ∈ K
    exact ⟨0, mem_closedBall_self hr.le, hCzero.trans hstart.symm⟩
  apply hAclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hA0
  intro t ht hprefix
  have hnorm : ‖C.symm (γ t)‖ < r := by
    rcases ht.1.eq_or_lt with rfl | htpos
    · rw [hstart, ← hCzero, C.left_inv hzero, norm_zero]
      exact hr
    · have hbound := frameExponential_inverse_path_length g o hRic e he C hzero hC hI
        γ 0 t htpos hγ.contMDiffOn (fun s hs => hKtarget (hprefix hs)) hstart
      have hlt : ENNReal.ofReal ‖C.symm (γ t)‖ < ENNReal.ofReal r :=
        hbound.trans_lt ((Manifold.pathELength_mono (I := I4) (γ := γ)
          le_rfl ht.2.le).trans_lt hlen)
      exact (ENNReal.ofReal_lt_ofReal_iff hr).mp hlt
  have htK : γ t ∈ K := hprefix ⟨ht.1, le_rfl⟩
  have htU : γ t ∈ U := ⟨C.symm (γ t), by simpa using hnorm,
    C.right_inv (hKtarget htK)⟩
  exact hγ.continuous.continuousWithinAt (mem_of_superset (hUopen.mem_nhds htU) hUK)

theorem frameExponential_normal_ball_distance_lower (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target) (r : ℝ) (hr : 0 < r)
    (hball : closedBall 0 r ⊆ C.source) (v : FourSpace) (hv : ‖v‖ < r) :
    ENNReal.ofReal ‖v‖ ≤ metricEDistance g e.base (frameExponential g o e v) := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  by_contra h
  have hlt : Manifold.riemannianEDist I4 e.base (frameExponential g o e v) <
      ENNReal.ofReal ‖v‖ := lt_of_not_ge h
  obtain ⟨γ, hstart, hend, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
  have hrlen : Manifold.pathELength I4 γ 0 1 < ENNReal.ofReal r :=
    hlen.trans (ENNReal.ofReal_lt_ofReal_iff hr |>.mpr hv)
  have hstay := frameExponential_short_path_stays g o hRic e he C hC hI r hr hball
    γ hγ hstart hrlen
  have htarget : MapsTo γ (Icc 0 1) C.target := by
    intro t ht
    obtain ⟨w, hw, hweq⟩ := hstay ht
    rw [← hweq]
    exact C.map_source (hball hw)
  have hzero : (0 : FourSpace) ∈ C.source := hball (mem_closedBall_self hr.le)
  have hbound := frameExponential_inverse_path_length g o hRic e he C hzero hC hI
    γ 0 1 zero_lt_one hγ.contMDiffOn htarget hstart
  have hvsource : v ∈ C.source := hball (by simpa using hv.le)
  have hinverse : C.symm (γ 1) = v := by
    rw [hend, ← hC hvsource]
    exact C.left_inv hvsource
  rw [hinverse] at hbound
  exact (not_lt_of_ge hbound) hlen

/-- The metric ball is covered by the actual radial normal coordinates. -/
theorem frameExponential_metric_ball_surj (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target) (r : ℝ) (hr : 0 < r)
    (hball : closedBall 0 r ⊆ C.source) (y : M)
    (hy : metricEDistance g e.base y < ENNReal.ofReal r) :
    ∃ v : FourSpace, ‖v‖ < r ∧ frameExponential g o e v = y ∧
      metricEDistance g e.base y = ENNReal.ofReal ‖v‖ := by
  let : RiemannianBundle (TangentSpace I4 : M → Type _) := ⟨g.toRiemannianMetric⟩
  obtain ⟨γ, hstart, hend, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hy zero_lt_one
  have hstay := frameExponential_short_path_stays g o hRic e he C hC hI r hr hball
    γ hγ hstart hlen
  have htarget : MapsTo γ (Icc 0 1) C.target := by
    intro t ht
    obtain ⟨v, hv, hvγ⟩ := hstay ht
    rw [← hvγ]
    exact C.map_source (hball hv)
  have hzero : (0 : FourSpace) ∈ C.source := hball (mem_closedBall_self hr.le)
  have hb := frameExponential_inverse_path_length g o hRic e he C hzero hC hI
    γ 0 1 zero_lt_one hγ.contMDiffOn htarget hstart
  let v := C.symm y
  have hv : ‖v‖ < r := by
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mp
    simpa only [hend] using hb.trans_lt hlen
  have hyC : y ∈ C.target := by simpa only [hend] using htarget (right_mem_Icc.mpr zero_le_one)
  have hexp : frameExponential g o e v = y :=
    (hC (C.map_target hyC)).symm.trans (C.right_inv hyC)
  refine ⟨v, hv, hexp, ?_⟩
  rw [← hexp]
  exact le_antisymm (frameExponential_distance g o e v)
    (frameExponential_normal_ball_distance_lower g o hRic e he C hC hI r hr hball v hv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual metric balls and spheres in a normal neighborhood are
precisely the images of Euclidean balls and spheres under the exponential. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Set Metric
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponential_image_closedBall (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target) (R : ℝ) (hR : 0 < R)
    (hball : closedBall 0 R ⊆ C.source) (r : ℝ) (hr : 0 ≤ r) (hrR : r < R) :
    frameExponential g o e '' closedBall 0 r =
      {y | metricEDistance g e.base y ≤ ENNReal.ofReal r} := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : ‖v‖ ≤ r := by simpa using hv
    exact (frameExponential_distance g o e v).trans (ENNReal.ofReal_le_ofReal hv')
  · intro hy
    have hyR : metricEDistance g e.base y < ENNReal.ofReal R :=
      hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR)
    obtain ⟨v, _, hvy, hvdist⟩ :=
      frameExponential_metric_ball_surj g o hRic e he C hC hI R hR hball y hyR
    have hv : ‖v‖ ≤ r := (ENNReal.ofReal_le_ofReal_iff hr).mp (hvdist ▸ hy)
    exact ⟨v, by simpa using hv, hvy⟩

theorem frameExponential_image_sphere (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (C : OpenPartialHomeomorph FourSpace M)
    (hC : EqOn C (frameExponential g o e) C.source)
    (hI : ContMDiffOn I4 I4 1 C.symm C.target) (R : ℝ) (hR : 0 < R)
    (hball : closedBall 0 R ⊆ C.source) (r : ℝ) (hr : 0 ≤ r) (hrR : r < R) :
    frameExponential g o e '' sphere 0 r =
      {y | metricEDistance g e.base y = ENNReal.ofReal r} := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : ‖v‖ = r := by simpa using hv
    have hvr : ‖v‖ < R := hv' ▸ hrR
    have hd := le_antisymm (frameExponential_distance g o e v)
      (frameExponential_normal_ball_distance_lower g o hRic e he C hC hI R hR hball v hvr)
    exact hd.trans (congrArg ENNReal.ofReal hv')
  · intro hy
    have hyR : metricEDistance g e.base y < ENNReal.ofReal R := by
      rw [hy]
      exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hrR
    obtain ⟨v, _, hvy, hvdist⟩ :=
      frameExponential_metric_ball_surj g o hRic e he C hC hI R hR hball y hyR
    have hv : ‖v‖ = r := (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) hr).mp
      (hvdist.symm.trans hy)
    exact ⟨v, by simpa using hv, hvy⟩

theorem exists_frameExponential_normal_ball_images (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) :
    ∃ R > (0 : ℝ), ∀ r : ℝ, 0 ≤ r → r < R →
      frameExponential g o e '' closedBall 0 r =
        {y | metricEDistance g e.base y ≤ ENNReal.ofReal r} ∧
      frameExponential g o e '' sphere 0 r =
        {y | metricEDistance g e.base y = ENNReal.ofReal r} := by
  obtain ⟨T, C, hT, hs, hC, hI⟩ := frameExponential_normal_ball g o e
  have hball : closedBall 0 (T / 2) ⊆ C.source := by
    rw [hs]
    exact closedBall_subset_ball (by linarith)
  refine ⟨T / 2, half_pos hT, fun r hr hrT => ?_⟩
  exact ⟨frameExponential_image_closedBall g o hRic e he C hC hI _ (half_pos hT)
    hball r hr hrT, frameExponential_image_sphere g o hRic e he C hC hI _ (half_pos hT)
    hball r hr hrT⟩

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

theorem frameGeodesic_minimizing_split_extends (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (q : M) (a : ℝ) (ha : 0 < a)
    (had : a < metricDistance g e.base q)
    (hmin : metricDistance g e.base (frameGeodesic g 0 e a) = a)
    (hsplit : metricDistance g e.base q =
      a + metricDistance g (frameGeodesic g 0 e a) q) :
    ∃ b > (0 : ℝ), a + b < metricDistance g e.base q ∧
      metricDistance g e.base (frameGeodesic g 0 e (a + b)) = a + b ∧
      metricDistance g e.base q =
        (a + b) + metricDistance g (frameGeodesic g 0 e (a + b)) q := by
  let f := parallelFrameFlowMap g 0 a e
  have hf : f ∈ o.positive := parallelFrameFlowMap_positive g o e he a
  obtain ⟨R, hR, himage⟩ := exists_frameExponential_normal_ball_images g o hRic f hf
  let b := min R (metricDistance g e.base q - a) / 2
  have hb : 0 < b := half_pos (lt_min hR (sub_pos.mpr had))
  have hbm : b < min R (metricDistance g e.base q - a) :=
    half_lt_self (lt_min hR (sub_pos.mpr had))
  have hbR : b < R := hbm.trans_le (min_le_left _ _)
  have hbd : a + b < metricDistance g e.base q := by
    have := hbm.trans_le (min_le_right _ _)
    linarith
  have hbf : b ≤ metricDistance g f.base q := by
    change b ≤ metricDistance g (frameGeodesic g 0 e a) q
    linarith
  obtain ⟨z, hzf, hzq⟩ := exists_metricDistance_real_split g f.base q b hb.le hbf
  have hzimage : z ∈ frameExponential g o f '' sphere 0 b := by
    rw [(himage b hb.le hbR).2]
    exact (metricDistance_eq_iff g f.base z hb.le).mp hzf
  obtain ⟨v, hv, hvz⟩ := hzimage
  have hvn : ‖v‖ = b := by simpa only [mem_sphere, dist_zero_right] using hv
  let w := b⁻¹ • v
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb), hvn, inv_mul_cancel₀ hb.ne']
  have hbw : b • w = v := by simp [w, smul_smul, hb.ne']
  have hpz : metricDistance g e.base z = a + b := by
    have ht := metricDistance_triangle g e.base f.base z
    have hu := metricDistance_triangle g e.base z q
    change metricDistance g e.base (frameGeodesic g 0 e a) = a at hmin
    change metricDistance g e.base q = a + metricDistance g f.base q at hsplit
    change metricDistance g e.base z ≤ metricDistance g e.base (frameGeodesic g 0 e a) +
      metricDistance g f.base z at ht
    linarith
  have hback : frameExponential g o f ((-a) • coordinateVector 0) = e.base := by
    rw [frameExponential_shift_first g o e he (-a) a, neg_add_cancel]
    exact congrArg FrameBundle.base (parallelFrameFlowMap_zero g 0 e)
  have hcorner : coordinateVector 0 = w := by
    apply frameExponential_no_minimizing_corner g o f (coordinateVector 0) w
      firstDirection.property hw a b ha hb
    rw [hback, hbw, hvz]
    exact (metricDistance_eq_iff g e.base z (by positivity : 0 ≤ a + b)).mp hpz
  have hz : z = frameGeodesic g 0 e (a + b) := by
    rw [← hvz, ← hbw, ← hcorner, frameExponential_shift_first g o e he b a, add_comm]
  refine ⟨b, hb, hbd, ?_, ?_⟩
  · rwa [← hz]
  · rw [← hz]
    change metricDistance g e.base q = a + metricDistance g f.base q at hsplit
    linarith

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

theorem frameExponential_metric_jacobian_direction (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (q : Directions) (d : M) (t : ℝ) (ht : 0 < t)
    (hd : frameExponential g o e (t • q.val) ∈ (chartAt FourSpace d).source) :
    chartVolumeDensity g d (chartAt FourSpace d (frameExponential g o e (t • q.val))) *
      |LinearMap.det (fderiv ℝ (fun v : FourSpace => chartAt FourSpace d
        (frameExponential g o e v)) (t • q.val)).toLinearMap| =
      |((actualJacobiSolution g hRic
        (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J t).det / t ^ 3| := by
  let Q := directionOrientedMatrix q
  let f := e.rotate (orientedToOrthogonal Q)
  have hf : f ∈ o.positive := frameRotate_oriented_positive o e he Q
  have hdir : orthogonalEuclideanIsometry (orientedToOrthogonal Q).val
      (orientedToOrthogonal Q).property (t • coordinateVector 0) = t • q.val := by
    rw [map_smul, directionRotation_first]
  have hpoint : frameExponential g o e (t • q.val) = (parallelFrameFlowMap g 0 t f).base :=
    frameExponential_direction_ray g o e he q t
  have hdf : (parallelFrameFlowMap g 0 t f).base ∈ (chartAt FourSpace d).source :=
    hpoint ▸ hd
  have hdet := frameExponential_chart_det_rotate g o e Q d (t • coordinateVector 0)
    (by rwa [hdir])
  rw [hdir] at hdet
  rw [← hdet, hpoint]
  exact frameExponential_metric_jacobian g o hRic d f hf t ht hdf

end
end PositiveEinsteinFour.Geometry
end


section

/-! Polar coordinates for the actual minimizing-domain Jacobian integral.
The radial cutoff is the proved cut time, not a supplied geometric domain. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem frameExponentialJacobian_direction (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) (e : FrameBundle g) (he : e ∈ o.positive)
    (q : Directions) (r : ℝ) (hr : 0 < r) :
    frameExponentialJacobian g o e (r • q.val) =
      |((actualJacobiSolution g hRic
        (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r).det / r ^ 3| := by
  let c := frameExponential g o e (r • q.val)
  rw [frameExponentialJacobian_chart g o e c (r • q.val) (mem_chart_source FourSpace c)]
  exact frameExponential_metric_jacobian_direction g o hRic e he q c r hr
    (mem_chart_source FourSpace c)

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Weighted exponential-area domination.  The weight is retained through
actual polar coordinates, for use with scalar oscillations and energy. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Angular MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]

theorem minimizing_exponential_weighted_radial (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g) (e : FrameBundle g)
    (he : e ∈ o.positive) (W : M → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ v in actualMinimizingTangentDomain g o e,
      ENNReal.ofReal (frameExponentialJacobian g o e v) * W (frameExponential g o e v)) =
    polarAngularMass * ∫⁻ q : Directions, ∫⁻ r : Ioi (0 : ℝ),
      (if r.val ≤ actualCutTime g
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q))) then
        ENNReal.ofReal |((actualJacobiSolution g hRic
          (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))).J r.val).det| *
            W (frameExponential g o e (r.val • q.val))
        else 0) ∂((volume : Measure ℝ).comap Subtype.val) ∂sphereMeasure := by
  classical
  let S := actualMinimizingTangentDomain g o e
  let F := fun v => ENNReal.ofReal (frameExponentialJacobian g o e v) *
    W (frameExponential g o e v)
  have hS : MeasurableSet S := (actualMinimizingTangentDomain_closed g o e).measurableSet
  have hF : Measurable F :=
    ((ENNReal.continuous_ofReal.comp (frameExponentialJacobian_continuous g o e)).measurable).mul
      (hW.comp (frameExponential_continuous g o e).measurable)
  rw [← lintegral_indicator hS F, euclidean_lintegral_polar _ (hF.indicator hS)]
  congr 1
  apply lintegral_congr
  intro q
  apply lintegral_congr
  intro r
  have hiff := actualMinimizingTangentDomain_ray_iff g o e he q r.val r.property.le
  by_cases hc : r.val ≤ actualCutTime g
      (e.rotate (orientedToOrthogonal (directionOrientedMatrix q)))
  · have hm : r.val • q.val ∈ S := hiff.mpr hc
    rw [ite_eq_left hc, Set.indicator_of_mem hm]
    dsimp only [F]
    rw [frameExponentialJacobian_direction g o hRic e he q r.val r.property]
    exact radial_weight_cancel _ _ r.property _
  · have hm : r.val • q.val ∉ S := fun h => hc (hiff.mp h)
    rw [ite_eq_right hc, Set.indicator_of_notMem hm, mul_zero]

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity06
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartEnergy_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartEnergy_baseProbability
theorem scalarChart_norm_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : M → ℝ) (hf : MemLp f 2 (normalizedVolume g))
      (hchart : MemLp (fun z : FourSpace => f ((chartAt FourSpace c).symm z)) 2
        (volume.restrict K)),
      ‖hchart.toLp _‖ ≤ C * ‖hf.toLp f‖ := by
  obtain ⟨C, hC, hbound⟩ := scalarChart_eLpNorm_bound g c hK hKt
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f hf hchart
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hC hf.eLpNorm_ne_top) (hbound f)
  simpa only [Lp.norm_toLp, ENNReal.toReal_mul] using h

theorem scalarCoordinate_gradient_memLp (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (a : SmoothScalar (M := M)) (i : Fin 4) :
    MemLp (fun z : FourSpace =>
      partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z) 2
      (volume.restrict K) := by
  have hcont : ContinuousOn (fun z : FourSpace =>
      partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z) K := by
    intro z hz
    have hs : ContDiffAt ℝ ∞ (fun w => a.val ((chartAt FourSpace c).symm w)) z :=
      scalarCoordinates_contDiffAt a.property c z (hKt hz) (fun j => Fin.elim0 j)
    exact ((hs.fderiv_right (m := ∞) (by first | simp | exact_mod_cast le_top)).clm_apply
      (contDiffAt_const (c := coordinateVector i))).continuousAt.continuousWithinAt
  obtain ⟨A, hA, hbound⟩ := scalarCoordinate_gradient_sq_le_on_compact g c hK hKt i
  have hroot := scalarChartL2_compact g c (scalarEnergyRootL2 g a) hK hKt
  have hroot' : MemLp (fun z : FourSpace =>
      (scalarEnergyRoot g a) ((chartAt FourSpace c).symm z)) 2 (volume.restrict K) := by
    have he := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (scalarEnergyRoot g a)
    -- The chart comparison transfers the base almost-everywhere equality.
    have hzero := scalarChart_eLpNorm_bound g c hK hKt
    obtain ⟨B, _hB, hBbound⟩ := hzero
    have hdiff : eLpNorm (fun z : FourSpace =>
        scalarEnergyRootL2 g a ((chartAt FourSpace c).symm z) -
          (scalarEnergyRoot g a) ((chartAt FourSpace c).symm z)) 2 (volume.restrict K) = 0 := by
      apply le_antisymm
      swap
      · exact zero_le
      have hh := hBbound (fun x => scalarEnergyRootL2 g a x - (scalarEnergyRoot g a) x)
      have hz : (fun x => scalarEnergyRootL2 g a x - (scalarEnergyRoot g a) x) =ᵐ[normalizedVolume g] 0 :=
        he.mono (fun _ hx => sub_eq_zero.mpr hx)
      simpa only [eLpNorm_congr_ae hz, eLpNorm_zero, mul_zero] using hh
    have hcont2 : ContinuousOn (fun z : FourSpace =>
        (scalarEnergyRoot g a) ((chartAt FourSpace c).symm z)) K :=
      (scalarEnergyRoot g a).continuous.comp_continuousOn
        ((chartAt FourSpace c).continuousOn_symm.mono hKt)
    have hae := (eLpNorm_eq_zero_iff
      (hroot.aestronglyMeasurable.sub (hcont2.aestronglyMeasurable hK.isClosed.measurableSet))
      (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hdiff
    apply hroot.ae_eq
    filter_upwards [hae] with z hz
    exact sub_eq_zero.mp hz
  apply hroot'.of_le_mul (c := Real.sqrt A)
    (hcont.aestronglyMeasurable hK.isClosed.measurableSet)
  filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  change |partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z| ≤
    Real.sqrt A * |Real.sqrt (scalarDirichletDensity g a ((chartAt FourSpace c).symm z))|
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact scalarCoordinate_gradient_abs_le g c i A hA hbound a hz

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
def smoothScalarChartDerivative (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    SmoothScalar (M := M) →ₗ[ℝ] Lp ℝ 2 (volume.restrict K) where
  toFun a := (scalarCoordinate_gradient_memLp g c hK hKt a i).toLp _
  map_add' a b := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt (a + b) i),
      MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt a i),
      MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt b i),
      Lp.coeFn_add ((scalarCoordinate_gradient_memLp g c hK hKt a i).toLp _)
        ((scalarCoordinate_gradient_memLp g c hK hKt b i).toLp _),
      ae_restrict_mem hK.isClosed.measurableSet] with z hab ha hb hsum hz
    rw [hab, hsum]
    simp only [Pi.add_apply]
    rw [ha, hb]
    have hda := (scalarCoordinates_contDiffAt a.property c z (hKt hz)
      (fun j => Fin.elim0 j)).differentiableAt (by first | simp | exact_mod_cast le_top)
    have hdb := (scalarCoordinates_contDiffAt b.property c z (hKt hz)
      (fun j => Fin.elim0 j)).differentiableAt (by first | simp | exact_mod_cast le_top)
    change DifferentiableAt ℝ (fun w => a.val ((chartAt FourSpace c).symm w)) z at hda
    change DifferentiableAt ℝ (fun w => b.val ((chartAt FourSpace c).symm w)) z at hdb
    change (fderiv ℝ (fun w => a.val ((chartAt FourSpace c).symm w) +
      b.val ((chartAt FourSpace c).symm w)) z) (coordinateVector i) = _
    rw [fderiv_fun_add hda hdb]
    rfl
  map_smul' r a := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt (r • a) i),
      MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt a i),
      Lp.coeFn_smul r ((scalarCoordinate_gradient_memLp g c hK hKt a i).toLp _)] with z hra ha hs
    simp only [RingHom.id_apply]
    rw [hra, hs]
    simp only [Pi.smul_apply]
    rw [ha]
    change (fderiv ℝ (r • fun w => a.val ((chartAt FourSpace c).symm w)) z)
      (coordinateVector i) = _
    rw [fderiv_const_smul_field]
    rfl

theorem smoothScalarChartDerivative_bound (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : SmoothScalar (M := M),
      ‖smoothScalarChartDerivative g c hK hKt i a‖ ≤ C * ‖smoothScalarH1Map o d a‖ := by
  obtain ⟨A, hA, hAbound⟩ := scalarCoordinate_gradient_sq_le_on_compact g c hK hKt i
  obtain ⟨B, hB, hBbound⟩ := scalarChart_eLpNorm_bound g c hK hKt
  let C := ENNReal.ofReal (Real.sqrt A) * B
  have hC : C ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro a
  have hpoint : ∀ᵐ z ∂volume.restrict K,
      ‖partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z‖ ≤
        Real.sqrt A * ‖(scalarEnergyRoot g a) ((chartAt FourSpace c).symm z)‖ := by
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with z hz
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hn : 0 ≤ (scalarEnergyRoot g a) ((chartAt FourSpace c).symm z) := Real.sqrt_nonneg _
    rw [abs_of_nonneg hn]
    exact scalarCoordinate_gradient_abs_le g c i A hA hAbound a hz
  have hlocal := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hpoint 2
  have hglobal := hBbound (scalarEnergyRoot g a)
  have he : eLpNorm (scalarEnergyRoot g a) 2 (normalizedVolume g) =
      eLpNorm (scalarEnergyRootL2 g a) 2 (normalizedVolume g) := by
    exact (eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
      (normalizedVolume g) (scalarEnergyRoot g a))).symm
  have hbound : eLpNorm
      (fun z : FourSpace => partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z)
      2 (volume.restrict K) ≤ C * eLpNorm (scalarEnergyRootL2 g a) 2 (normalizedVolume g) := by
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt A) * _ := hlocal
      _ ≤ ENNReal.ofReal (Real.sqrt A) * (B * eLpNorm (scalarEnergyRoot g a) 2
          (normalizedVolume g)) := mul_le_mul' le_rfl hglobal
      _ = _ := by rw [he, mul_assoc]
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hC (Lp.eLpNorm_ne_top _)) hbound
  have hn : ‖smoothScalarChartDerivative g c hK hKt i a‖ ≤
      C.toReal * ‖scalarEnergyRootL2 g a‖ := by
    change ‖(scalarCoordinate_gradient_memLp g c hK hKt a i).toLp _‖ ≤ _
    rw [Lp.norm_toLp, Lp.norm_def]
    simpa only [ENNReal.toReal_mul] using hr
  exact hn.trans (mul_le_mul_of_nonneg_left (scalarEnergyRootL2_norm_le g o d a)
    ENNReal.toReal_nonneg)

def scalarH1ChartDerivative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (i : Fin 4) :
    scalarH1 d →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  (smoothScalarChartDerivative g c hK hKt i).extendOfNorm (smoothScalarH1Map o d)

theorem scalarH1ChartDerivative_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (i : Fin 4) (a : SmoothScalar (M := M)) :
    scalarH1ChartDerivative g o d c hK hKt i (smoothScalarToH1 d a) =
      smoothScalarChartDerivative g c hK hKt i a := by
  obtain ⟨C, _, hC⟩ := smoothScalarChartDerivative_bound g o d c hK hKt i
  exact LinearMap.extendOfNorm_eq (smoothScalarH1Map_dense o d) ⟨C, hC⟩ a

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartValue_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartValue_baseProbability
theorem scalarChart_ae_eq (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) {f h : M → ℝ}
    (heq : f =ᵐ[normalizedVolume g] h) :
    (fun z : FourSpace => f ((chartAt FourSpace c).symm z)) =ᵐ[volume.restrict K]
      (fun z : FourSpace => h ((chartAt FourSpace c).symm z)) := by
  obtain ⟨C, _, hC⟩ := scalarChart_eLpNorm_bound g c hK hKt
  have hdiff : (fun x => f x - h x) =ᵐ[normalizedVolume g] 0 :=
    heq.mono (fun _ hx => sub_eq_zero.mpr hx)
  -- `eLpNorm` of a non-measurable function is not controlled by its a.e. class here: route through a
  -- measurable null set carrying the disagreement of `f` and `h`
  obtain ⟨Z, hZsub, hZm, hZ0⟩ := exists_measurable_superset_of_null
    (show normalizedVolume g {x | f x ≠ h x} = 0 from heq)
  have hv := hC (Z.indicator fun _ => (1 : ℝ))
  have hv0 : eLpNorm (Z.indicator fun _ => (1 : ℝ)) 2 (normalizedVolume g) = 0 := by
    rw [eLpNorm_eq_zero_iff ((measurable_const.indicator hZm).aestronglyMeasurable) (by norm_num)]
    filter_upwards [compl_mem_ae_iff.mpr hZ0] with x hx
    simp [Set.indicator_of_notMem hx]
  have hle : eLpNorm (fun z : FourSpace =>
      (Z.indicator fun _ => (1 : ℝ)) ((chartAt FourSpace c).symm z)) 2 (volume.restrict K) = 0 := by
    apply le_antisymm
    · simpa [hv0] using hv
    · exact zero_le
  have hmeas : AEStronglyMeasurable (fun z : FourSpace =>
      (Z.indicator fun _ => (1 : ℝ)) ((chartAt FourSpace c).symm z)) (volume.restrict K) :=
    ((measurable_const.indicator hZm).comp_aemeasurable
      (((chartAt FourSpace c).continuousOn_symm.mono hKt).aemeasurable
        hK.isClosed.measurableSet)).aestronglyMeasurable
  have hz0 := (eLpNorm_eq_zero_iff hmeas (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hle
  filter_upwards [hz0] with z hz
  by_contra hne
  have hmem : (chartAt FourSpace c).symm z ∈ Z := hZsub hne
  simp [Set.indicator_of_mem hmem] at hz

def scalarChartValueLin (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    Lp ℝ 2 (normalizedVolume g) →ₗ[ℝ] Lp ℝ 2 (volume.restrict K) where
  toFun b := (scalarChartL2_compact g c b hK hKt).toLp _
  map_add' a b := by
    apply Lp.ext
    have hbase := scalarChart_ae_eq g c hK hKt (Lp.coeFn_add a b)
    filter_upwards [MemLp.coeFn_toLp (scalarChartL2_compact g c (a + b) hK hKt),
      MemLp.coeFn_toLp (scalarChartL2_compact g c a hK hKt),
      MemLp.coeFn_toLp (scalarChartL2_compact g c b hK hKt),
      Lp.coeFn_add ((scalarChartL2_compact g c a hK hKt).toLp _)
        ((scalarChartL2_compact g c b hK hKt).toLp _), hbase] with z hab ha hb hs he
    exact hab.trans (he.trans ((congrArg₂ (· + ·) ha hb).symm.trans hs.symm))
  map_smul' r b := by
    apply Lp.ext
    have hbase := scalarChart_ae_eq g c hK hKt (Lp.coeFn_smul r b)
    filter_upwards [MemLp.coeFn_toLp (scalarChartL2_compact g c (r • b) hK hKt),
      MemLp.coeFn_toLp (scalarChartL2_compact g c b hK hKt),
      Lp.coeFn_smul r ((scalarChartL2_compact g c b hK hKt).toLp _), hbase] with z hrb hb hs he
    exact hrb.trans (he.trans ((congrArg (r • ·) hb).symm.trans hs.symm))

theorem scalarChartValueLin_bound (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    ∃ C : ℝ, ∀ b : Lp ℝ 2 (normalizedVolume g),
      ‖scalarChartValueLin g c hK hKt b‖ ≤ C * ‖b‖ := by
  obtain ⟨C, _, hC⟩ := scalarChart_norm_bound g c hK hKt
  refine ⟨C, fun b => ?_⟩
  have h := hC b (Lp.memLp b) (scalarChartL2_compact g c b hK hKt)
  simpa only [scalarChartValueLin, LinearMap.coe_mk, AddHom.coe_mk, Lp.toLp_coeFn] using h

def scalarChartValue (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    Lp ℝ 2 (normalizedVolume g) →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  (scalarChartValueLin g c hK hKt).mkContinuousOfExistsBound
    (scalarChartValueLin_bound g c hK hKt)

theorem scalarChartValue_coe (g : SmoothMetric M) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (b : Lp ℝ 2 (normalizedVolume g)) :
    scalarChartValue g c hK hKt b =ᵐ[volume.restrict K]
      (fun z : FourSpace => b ((chartAt FourSpace c).symm z)) :=
  MemLp.coeFn_toLp (scalarChartL2_compact g c b hK hKt)

def scalarH1ChartValue (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) :
    scalarH1 d →L[ℝ] Lp ℝ 2 (volume.restrict K) :=
  (scalarChartValue g c hK hKt).comp (scalarH1BaseValue g o d)

theorem scalarH1ChartValue_coe (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (u : scalarH1 d)
    (b : Lp ℝ 2 (normalizedVolume g)) (hb : scalarBasePullback g o b = scalarH1Value d u) :
    scalarH1ChartValue g o d c hK hKt u =ᵐ[volume.restrict K]
      (fun z : FourSpace => b ((chartAt FourSpace c).symm z)) := by
  change scalarChartValue g c hK hKt (scalarH1BaseValue g o d u) =ᵐ[_] _
  rw [scalarH1BaseValue_eq g o d u b hb]
  exact scalarChartValue_coe g c hK hKt b

theorem scalarH1ChartValue_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (a : SmoothScalar (M := M)) :
    scalarH1ChartValue g o d c hK hKt (smoothScalarToH1 d a) =ᵐ[volume.restrict K]
      (fun z : FourSpace => a.val ((chartAt FourSpace c).symm z)) := by
  have h := scalarH1ChartValue_coe g o d c hK hKt (smoothScalarToH1 d a)
    (smoothScalarBaseL2 g a) (scalarBasePullback_smooth g o a)
  exact h.trans (scalarChart_ae_eq g c hK hKt
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (⟨a.val, a.property.continuous⟩ : C(M, ℝ))))

end
end PositiveEinsteinFour.Geometry
end


section

/-! The extended coordinate derivative is the weak derivative of the actual
chart representative, verified against genuine compact smooth tests. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.chartWeak_frameCompact
theorem scalarChart_smooth_weak_derivative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (a : SmoothScalar (M := M))
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ K) (i : Fin 4) :
    inner ℝ (scalarH1ChartValue g o d c hK hKt (smoothScalarToH1 d a))
      (scalarCompactDerivativeL2 K ψ hψ hc i) =
    -inner ℝ (scalarH1ChartDerivative g o d c hK hKt i (smoothScalarToH1 d a))
      (scalarCompactTestL2 K ψ hψ.continuous hc) := by
  have hval := scalarH1ChartValue_smooth g o d c hK hKt a
  have hgrad : scalarH1ChartDerivative g o d c hK hKt i (smoothScalarToH1 d a) =ᵐ[volume.restrict K]
      (fun z => partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z) := by
    rw [scalarH1ChartDerivative_smooth]
    exact MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt a i)
  have htest := scalarCompactTestL2_coe K ψ hψ.continuous hc
  have hDtest : scalarCompactDerivativeL2 K ψ hψ hc i =ᵐ[volume.restrict K]
      (fun z => partialDeriv ψ i z) := scalarCompactTestL2_coe ..
  have hDsupport : tsupport (fun z => partialDeriv ψ i z) ⊆ K :=
    (tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs
  have hleft : (∫ z in K, a.val ((chartAt FourSpace c).symm z) * partialDeriv ψ i z) =
      ∫ z, a.val ((chartAt FourSpace c).symm z) * partialDeriv ψ i z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hDsupport h)), mul_zero]
  have hright : (∫ z in K,
      partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z * ψ z) =
      ∫ z, partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z * ψ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hs h)), mul_zero]
  rw [scalar_real_L2_pairing, scalar_real_L2_pairing]
  have hl := integral_congr_ae (hval.mul hDtest)
  have hr := integral_congr_ae (hgrad.mul htest)
  simp only [Pi.mul_apply] at hl hr
  rw [hl, hr, hleft, hright]
  exact scalar_chart_integration_by_parts a c ψ hψ hc (hs.trans hKt) i

theorem scalarH1Chart_weak_derivative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (u : scalarH1 d)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ K) (i : Fin 4) :
    inner ℝ (scalarH1ChartValue g o d c hK hKt u)
      (scalarCompactDerivativeL2 K ψ hψ hc i) =
    -inner ℝ (scalarH1ChartDerivative g o d c hK hKt i u)
      (scalarCompactTestL2 K ψ hψ.continuous hc) := by
  have hclosed : IsClosed {v : scalarH1 d |
      inner ℝ (scalarH1ChartValue g o d c hK hKt v)
        (scalarCompactDerivativeL2 K ψ hψ hc i) =
      -inner ℝ (scalarH1ChartDerivative g o d c hK hKt i v)
        (scalarCompactTestL2 K ψ hψ.continuous hc)} :=
    isClosed_eq ((scalarH1ChartValue g o d c hK hKt).continuous.inner continuous_const)
      ((scalarH1ChartDerivative g o d c hK hKt i).continuous.inner continuous_const).neg
  exact (smoothScalarH1Map_dense o d).induction_on u hclosed
    (fun a => scalarChart_smooth_weak_derivative g o d c hK hKt a ψ hψ hc hs i)

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localWeak_frameCompact
theorem scalarH1Chart_weak_derivative_integral (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target) (u : scalarH1 d)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ K) (i : Fin 4) :
    (∫ z in K, scalarH1ChartValue g o d c hK hKt u z * partialDeriv ψ i z) =
      -(∫ z in K, scalarH1ChartDerivative g o d c hK hKt i u z * ψ z) := by
  have hw := scalarH1Chart_weak_derivative g o d c hK hKt u ψ hψ hc hs i
  simp only [L2.inner_def, RCLike.inner_apply', conj_trivial] at hw
  have hD : scalarCompactDerivativeL2 K ψ hψ hc i =ᵐ[volume.restrict K]
      (fun z => partialDeriv ψ i z) := scalarCompactTestL2_coe ..
  have ht := scalarCompactTestL2_coe K ψ hψ.continuous hc
  have he₁ := integral_congr_ae ((Filter.EventuallyEq.rfl
    (f := fun z => scalarH1ChartValue g o d c hK hKt u z)).mul hD)
  have he₂ := integral_congr_ae ((Filter.EventuallyEq.rfl
    (f := fun z => scalarH1ChartDerivative g o d c hK hKt i u z)).mul ht)
  simp only [Pi.mul_apply] at he₁ he₂
  rwa [he₁, he₂] at hw

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ScalarRegularity07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.complexCoordinates_frameCompact
theorem scalarH1Chart_cutoff_memSobolev_one (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (u : scalarH1 d) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ K) :
    MemSobolev 1 2 (scalarComplexL2 (scalarLocalL2Product hK.measurableSet χ
      hχ.continuous hc hs (scalarH1ChartValue g o d c hK hKt u)) :
        𝓢'(FourSpace, ℂ)) := by
  rw [← zero_add (1 : ℝ)]
  apply (scalar_memSobolev_succ_iff 0 _).mpr
  constructor
  · exact memSobolev_zero_iff.mpr ⟨_, rfl⟩
  · intro i
    rw [scalarLocalL2_complex_derivative hK.measurableSet _
      (scalarH1ChartDerivative g o d c hK hKt i u) i
      (fun q hq hqc hqs => scalarH1Chart_weak_derivative_integral
        g o d c hK hKt u q hq hqc hqs i) χ hχ hc hs]
    exact memSobolev_zero_iff.mpr ⟨_, rfl⟩

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

local instance instFactLeENNRealOfNat_solutions_3_r33aabd_1 : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localSobolev_frameCompact
def scalarH1CutoffDerivative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (i : Fin 4) :
    scalarH1 d →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarLocalL2ProductCLM hK.isClosed.measurableSet χ hχ.continuous hc hs).comp
      (scalarH1ChartDerivative g o d c hK hKt i) +
    (scalarLocalL2ProductCLM hK.isClosed.measurableSet (partialDeriv χ i)
      (((hχ.fderiv_right (m := ∞) (by simp)).clm_apply
        (contDiff_const (c := coordinateVector i))).continuous)
      (hc.fderiv_apply ℝ (coordinateVector i))
      ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs)).comp
      (scalarH1ChartValue g o d c hK hKt)

theorem scalarH1CutoffDerivative_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : SmoothScalar (M := M)) (i : Fin 4) :
    scalarH1CutoffDerivative g o d c hK hKt χ hχ hc hs i (smoothScalarToH1 d a) =
      ScalarEuclideanSobolev.partialL2 (scalarCutoffChartC1 c hKt χ hχ hc hs a) i := by
  let P := scalarLocalL2ProductCLM hK.isClosed.measurableSet χ hχ.continuous hc hs
  let Q := scalarLocalL2ProductCLM hK.isClosed.measurableSet (partialDeriv χ i)
    (((hχ.fderiv_right (m := ∞) (by simp)).clm_apply
      (contDiff_const (c := coordinateVector i))).continuous)
    (hc.fderiv_apply ℝ (coordinateVector i))
    ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs)
  have hD : P (scalarH1ChartDerivative g o d c hK hKt i (smoothScalarToH1 d a)) =ᵐ[volume]
      (fun z => χ z * partialDeriv (fun w => a.val ((chartAt FourSpace c).symm w)) i z) := by
    rw [scalarH1ChartDerivative_smooth]
    exact (scalarLocalL2ProductCLM_coe ..).trans
      (scalarLocalL2Product_ae_congr hK.isClosed.measurableSet χ hs
        (MemLp.coeFn_toLp (scalarCoordinate_gradient_memLp g c hK hKt a i)))
  have hV : Q (scalarH1ChartValue g o d c hK hKt (smoothScalarToH1 d a)) =ᵐ[volume]
      (fun z => partialDeriv χ i z * a.val ((chartAt FourSpace c).symm z)) :=
    (scalarLocalL2ProductCLM_coe ..).trans
      (scalarLocalL2Product_ae_congr hK.isClosed.measurableSet (partialDeriv χ i)
        ((tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hs)
        (scalarH1ChartValue_smooth g o d c hK hKt a))
  apply Lp.ext
  have hsum := Lp.coeFn_add
    (P (scalarH1ChartDerivative g o d c hK hKt i (smoothScalarToH1 d a)))
    (Q (scalarH1ChartValue g o d c hK hKt (smoothScalarToH1 d a)))
  filter_upwards [hD, hV, hsum,
    ScalarEuclideanSobolev.partialL2_coe (scalarCutoffChartC1 c hKt χ hχ hc hs a) i]
      with z hDz hVz hsz hpz
  change ((P _ + Q _) : Lp ℝ 2 (volume : Measure FourSpace)) z = _
  exact hsz.trans (by
    rw [Pi.add_apply, hDz, hVz, hpz, scalarCutoffChart_partial])

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
def scalarWeightedChartL2 (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (u : scalarH1 d) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ K) :
    Lp ℝ 2 (volume : Measure FourSpace) :=
  scalarLocalL2Product hK.measurableSet (fun z => χ z * chartVolumeDensity g c z)
    (scalarDensityCutoff_smooth g c χ hχ (hs.trans hKt)).continuous
    hc.mul_right (tsupport_mul_subset_left.trans hs)
    (scalarH1ChartValue g o d c hK hKt u)

theorem scalarWeightedChartL2_memSobolev_one (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (u : scalarH1 d) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ K) :
    MemSobolev 1 2 (scalarComplexL2 (scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs) :
      𝓢'(FourSpace, ℂ)) := by
  exact scalarH1Chart_cutoff_memSobolev_one g o d c hK hKt u
    (fun z => χ z * chartVolumeDensity g c z)
    (scalarDensityCutoff_smooth g c χ hχ (hs.trans hKt))
    hc.mul_right (tsupport_mul_subset_left.trans hs)

theorem scalarWeightedChartL2_coe (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (u : scalarH1 d) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ K) :
    scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs =ᵐ[volume]
      (fun z => χ z * chartVolumeDensity g c z *
        scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z)) := by
  have hb := scalarH1ChartValue_coe g o d c hK hKt u (scalarH1BaseValue g o d u)
    (scalarH1BaseValue_spec g o d u)
  have hb' := (ae_restrict_iff' hK.measurableSet).mp hb
  have he := scalarLocalL2Product_coe hK.measurableSet
    (fun z => χ z * chartVolumeDensity g c z)
    (scalarDensityCutoff_smooth g c χ hχ (hs.trans hKt)).continuous
    hc.mul_right (tsupport_mul_subset_left.trans hs)
    (scalarH1ChartValue g o d c hK hKt u)
  filter_upwards [he, hb'] with z hz hzb
  change scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs z =
    χ z * chartVolumeDensity g c z * scalarH1ChartValue g o d c hK hKt u z at hz
  rw [hz]
  by_cases h : z ∈ K
  · rw [hzb h]
  · rw [image_eq_zero_of_notMem_tsupport (fun ht => h (hs ht))]
    simp only [zero_mul]

theorem scalarWeightedChartL2_integral (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (u : scalarH1 d) (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ K) (ψ : FourSpace → ℝ) :
    (∫ z, scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs z * ψ z) =
      ∫ z, χ z * chartVolumeDensity g c z *
        scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z) * ψ z :=
  integral_congr_ae ((scalarWeightedChartL2_coe g o d c hK hKt u χ hχ hc hs).mono
    (fun _ hz => congrArg (· * _) hz))

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.euclideanJet_frameCompact
def scalarH1CutoffValueL2 (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) :
    scalarH1 d →L[ℝ] Lp ℝ 2 (volume : Measure FourSpace) :=
  (scalarLocalL2ProductCLM hK.isClosed.measurableSet χ hχ.continuous hc hs).comp
    (scalarH1ChartValue g o d c hK hKt)

theorem scalarH1CutoffValueL2_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : SmoothScalar (M := M)) :
    scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs (smoothScalarToH1 d a) =
      ScalarEuclideanSobolev.valueL2 (scalarCutoffChartC1 c hKt χ hχ hc hs a) := by
  apply Lp.ext
  have he := (scalarLocalL2ProductCLM_coe hK.isClosed.measurableSet χ hχ.continuous hc hs
      (scalarH1ChartValue g o d c hK hKt (smoothScalarToH1 d a))).trans
    (scalarLocalL2Product_ae_congr hK.isClosed.measurableSet χ hs
      (scalarH1ChartValue_smooth g o d c hK hKt a))
  filter_upwards [he,
    ScalarEuclideanSobolev.valueL2_coe (scalarCutoffChartC1 c hKt χ hχ hc hs a)]
      with z hz hv
  exact hz.trans hv.symm

/-- Assemble the four bounded weak coordinate derivative maps into the
ordinary Euclidean vector gradient. -/
def scalarH1CutoffGradientL2 (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) :
    scalarH1 d →L[ℝ] Lp FourSpace 2 (volume : Measure FourSpace) :=
  ∑ i : Fin 4, (ScalarEuclideanSobolev.coordinateL2 i).comp
    (scalarH1CutoffDerivative g o d c hK hKt χ hχ hc hs i)

theorem scalarH1CutoffGradientL2_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K) (a : SmoothScalar (M := M)) :
    scalarH1CutoffGradientL2 g o d c hK hKt χ hχ hc hs (smoothScalarToH1 d a) =
      ScalarEuclideanSobolev.gradientL2 (scalarCutoffChartC1 c hKt χ hχ hc hs a) := by
  rw [ScalarEuclideanSobolev.gradientL2_eq_sum_partialL2]
  simp only [scalarH1CutoffGradientL2, sum_apply,
    ContinuousLinearMap.comp_apply, scalarH1CutoffDerivative_smooth]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Poisson equation tested against compact coordinate
functions, with the volume density absorbed into the same H1 solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.weightedTests_frameCompact
theorem scalarWeightedChartL2_test_equation (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : SmoothScalar (M := M)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
          (scalarH1Value d v)))
    (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψt : tsupport ψ ⊆ (chartAt FourSpace c).target)
    (hone : ∀ z ∈ tsupport ψ, χ z = 1) :
    (∫ z, scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs z *
      scalarChartOperator g c ψ z) =
      ∫ z, chartVolumeDensity g c z *
        (f.val ((chartAt FourSpace c).symm z) * ψ z) := by
  rw [scalarWeightedChartL2_integral]
  calc
    _ = ∫ z, chartVolumeDensity g c z *
        (scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z) *
          scalarChartOperator g c ψ z) := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ tsupport ψ
      · rw [hone z hz]
        ring
      · rw [scalarChartOperator_eq_zero_off_tsupport g c ψ hz]
        ring
    _ = ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z) *
          scalarChartOperator g c ψ z) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [scalarChartOperator_eq_zero_off_tsupport g c ψ (fun h => hz (hψt h))]
      ring
    _ = ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (f.val ((chartAt FourSpace c).symm z) * ψ z) :=
      scalarH1_weak_coordinate_distribution g o d f u hw c ψ hψ hψc hψt
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hψt h))]
      ring

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.manifoldSobolev_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.manifoldSobolev_probability
def scalarH1BaseL4 (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    scalarH1 d →L[ℝ] Lp ℝ 4 (normalizedVolume g) :=
  (smoothScalarBaseL4 g).extendOfNorm (smoothScalarH1Map o d)

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
  {K : Set FourSpace} (hK : IsCompact K) (hKt : K ⊆ (chartAt FourSpace c).target)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (hs : tsupport χ ⊆ K)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFourSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFourSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instMeasureSpaceFourSpace
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.rellichLocalization_frameCompact
def scalarH1BorelCutoffJet :
    scalarH1 d →L[ℝ] Euclidean.H1Target (μ := (volume : Measure FourSpace)) :=
  ((scalarBorelLpEquiv ℝ 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs)).prod
  ((scalarBorelLpEquiv FourSpace 2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scalarH1CutoffGradientL2 g o d c hK hKt χ hχ hc hs))

theorem scalarH1BorelCutoffJet_smooth (a : SmoothScalar (M := M)) :
    scalarH1BorelCutoffJet g o d c hK hKt χ hχ hc hs (smoothScalarToH1 d a) =
      Euclidean.graph (μ := (volume : Measure FourSpace))
        (scalarCutoffChartC1 c hKt χ hχ hc hs a) := by
  apply Prod.ext
  · change scalarBorelLpEquiv ℝ 2
      (scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs (smoothScalarToH1 d a)) = _
    rw [scalarH1CutoffValueL2_smooth, scalarBorel_valueL2]
    rfl
  · change scalarBorelLpEquiv FourSpace 2
      (scalarH1CutoffGradientL2 g o d c hK hKt χ hχ hc hs (smoothScalarToH1 d a)) = _
    rw [scalarH1CutoffGradientL2_smooth, scalarBorel_gradientL2]
    rfl

theorem scalarH1BorelCutoffJet_mem (u : scalarH1 d) :
    scalarH1BorelCutoffJet g o d c hK hKt χ hχ hc hs u ∈
      Euclidean.h1 (μ := (volume : Measure FourSpace)) := by
  refine (smoothScalarH1Map_dense o d).induction_on
    (p := fun v => scalarH1BorelCutoffJet g o d c hK hKt χ hχ hc hs v ∈
      Euclidean.h1 (μ := (volume : Measure FourSpace))) u ?_ ?_
  · exact (Euclidean.isClosed_h1 (μ := (volume : Measure FourSpace))).preimage
      (scalarH1BorelCutoffJet g o d c hK hKt χ hχ hc hs).continuous
  · intro a
    change scalarH1BorelCutoffJet g o d c hK hKt χ hχ hc hs (smoothScalarToH1 d a) ∈ _
    rw [scalarH1BorelCutoffJet_smooth]
    exact Submodule.le_topologicalClosure _ ⟨_, rfl⟩

def scalarH1CutoffEuclideanH1 :
    scalarH1 d →L[ℝ] ↥(Euclidean.h1 (μ := (volume : Measure FourSpace))) :=
  (scalarH1BorelCutoffJet g o d c hK hKt χ hχ hc hs).codRestrict _
    (scalarH1BorelCutoffJet_mem g o d c hK hKt χ hχ hc hs)

theorem scalarH1CutoffEuclideanH1_supported (u : scalarH1 d) :
    scalarH1CutoffEuclideanH1 g o d c hK hKt χ hχ hc hs u ∈
      Euclidean.h1On K hK.isClosed.measurableSet := by
  refine (smoothScalarH1Map_dense o d).induction_on
    (p := fun v => scalarH1CutoffEuclideanH1 g o d c hK hKt χ hχ hc hs v ∈
      Euclidean.h1On K hK.isClosed.measurableSet) u ?_ ?_
  · exact (Euclidean.isClosed_range_extendByZero K hK.isClosed.measurableSet).preimage
      ((Euclidean.h1ToL2 (μ := (volume : Measure FourSpace))).comp
        (scalarH1CutoffEuclideanH1 g o d c hK hKt χ hχ hc hs)).continuous
  · intro a
    change (scalarH1BorelCutoffJet g o d c hK hKt χ hχ hc hs
      (smoothScalarToH1 d a)).1 ∈
        LinearMap.range ((Lp.extendByZeroₗᵢ
          (μ := (volume : Measure FourSpace)) (E := ℝ) (p := 2)
          (s := K) hK.isClosed.measurableSet).toLinearMap)
    rw [scalarH1BorelCutoffJet_smooth]
    exact Euclidean.mem_range_extendByZeroₗᵢ_toLp_of_tsupport_subset
      (μ := (volume : Measure FourSpace)) hK.isClosed.measurableSet
      (scalarCutoffChartC1 c hKt χ hχ hc hs a).val
      (Euclidean.memLp_of_mem_C1c (μ := (volume : Measure FourSpace))
        (scalarCutoffChartC1 c hKt χ hχ hc hs a).property)
      ((tsupport_mul_subset_left).trans hs)

def scalarH1CutoffSupportedH1 :
    scalarH1 d →L[ℝ] ↥(Euclidean.h1On K hK.isClosed.measurableSet) :=
  (scalarH1CutoffEuclideanH1 g o d c hK hKt χ hχ hc hs).codRestrict _
    (scalarH1CutoffEuclideanH1_supported g o d c hK hKt χ hχ hc hs)

/-- Compactness of a fixed chart cutoff, in the original Lebesgue L² space. -/
theorem scalarH1CutoffValueL2_compact :
    IsCompactOperator (scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs) := by
  have h := (Euclidean.isCompactOperator_h1OnToL2 hK hK.isClosed.measurableSet).comp_clm
    (scalarH1CutoffSupportedH1 g o d c hK hKt χ hχ hc hs)
  have h' := h.clm_comp
    (scalarBorelLpEquiv ℝ 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  convert h' using 1
  all_goals try with_reducible_and_instances rfl
  funext u
  change scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs u =
    (scalarBorelLpEquiv ℝ 2).symm
      (scalarBorelLpEquiv ℝ 2 (scalarH1CutoffValueL2 g o d c hK hKt χ hχ hc hs u))
  exact ((scalarBorelLpEquiv ℝ 2).symm_apply_apply _).symm

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.rescaledTests_frameCompact
theorem scalarRescaled_test_equation (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : SmoothScalar (M := M)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
          (scalarH1Value d v)))
    (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψt : ∀ y ∈ tsupport ψ,
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target)
    (hone : ∀ y ∈ tsupport ψ, χ (scalarRescaledPoint g c z₀ r y) = 1) :
    (∫ y, scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ r hr) z₀
        (scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs) y *
          scalarRescaledOperator g c z₀ r ψ y) =
      ∫ y, r ^ 2 * chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
        f.val ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y)) * ψ y := by
  let A := scalarRescalingLinearEquiv g c z₀ r hr
  let ψ₀ : FourSpace → ℝ := fun z => ψ (A.symm (z - z₀))
  have hp : ContDiff ℝ ∞ ψ₀ :=
    hψ.comp (A.symm.contDiff.comp (contDiff_id.sub contDiff_const))
  have hpc : HasCompactSupport ψ₀ := by
    have h := hψc.comp_homeomorph
      ((Homeomorph.addRight (-z₀.val)).trans A.symm.toHomeomorph)
    change HasCompactSupport (fun z => ψ (A.symm (z + -z₀.val))) at h
    simpa only [ψ₀, sub_eq_add_neg] using h
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ r (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ r hr]
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hps {z : FourSpace} (hz : z ∈ tsupport ψ₀) : A.symm (z - z₀) ∈ tsupport ψ :=
    tsupport_comp_subset_preimage (f := fun z => A.symm (z - z₀)) ψ (by fun_prop) hz
  have hpt : tsupport ψ₀ ⊆ (chartAt FourSpace c).target := by
    intro z hz
    have h := hψt _ (hps hz)
    rwa [hinv] at h
  have hpo : ∀ z ∈ tsupport ψ₀, χ z = 1 := by
    intro z hz
    have h := hone _ (hps hz)
    rwa [hinv] at h
  have heq := scalarWeightedChartL2_test_equation g o d f u hw c hK hKt
    χ hχ hc hs ψ₀ hp hpc hpt hpo
  have hop (z : FourSpace) : scalarRescaledOperator g c z₀ r ψ (A.symm (z - z₀)) =
      r ^ 2 * scalarChartOperator g c ψ₀ z := by
    have h := scalarRescaledOperator_eq_chart g c z₀ r hr ψ hψ (A.symm (z - z₀))
    rw [hinv] at h
    exact h.symm
  rw [scalarAffineL2_integral]
  change scalarAffineJacobian A * (∫ z, _ * scalarRescaledOperator g c z₀ r ψ
    (A.symm (z - z₀))) = _
  simp_rw [hop]
  have hmul : (∫ z, scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs z *
      (r ^ 2 * scalarChartOperator g c ψ₀ z)) =
      r ^ 2 * ∫ z, scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs z *
        scalarChartOperator g c ψ₀ z := by
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  rw [hmul, heq]
  have hsource := scalarAffine_integral A z₀.val (fun z =>
    chartVolumeDensity g c z * (f.val ((chartAt FourSpace c).symm z) * ψ₀ z))
  have htest (y : FourSpace) : ψ₀ (A y + z₀) = ψ y := by
    simp only [ψ₀, add_sub_cancel_right, A.symm_apply_apply]
  change (∫ y, chartVolumeDensity g c (A y + z₀) *
    (f.val ((chartAt FourSpace c).symm (A y + z₀)) * ψ₀ (A y + z₀))) = _ at hsource
  have hpoint (y : FourSpace) : A y + z₀ = scalarRescaledPoint g c z₀ r y :=
    scalarRescalingLinearEquiv_apply g c z₀ r hr y
  have htest' (y : FourSpace) : ψ₀ (scalarRescaledPoint g c z₀ r y) = ψ y := by
    rw [← hpoint, htest]
  simp only [hpoint, htest'] at hsource
  rw [mul_left_comm (scalarAffineJacobian A) (r ^ 2), ← hsource,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual weak Poisson equation tested against compact coordinate
functions, with the volume density absorbed into the same H1 solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Filter
open scoped Manifold ContDiff _root_.Topology BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable [T3Space M] [CompactSpace M] [Nonempty M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.weightedL2Tests_frameCompact
theorem scalarWeightedChartL2_L2_test_equation (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : Lp ℝ 2 (normalizedVolume g)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarBasePullback g o f)
          (scalarH1Value d v)))
    (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψt : tsupport ψ ⊆ (chartAt FourSpace c).target)
    (hone : ∀ z ∈ tsupport ψ, χ z = 1) :
    (∫ z, scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs z *
      scalarChartOperator g c ψ z) =
      ∫ z, chartVolumeDensity g c z *
        (f ((chartAt FourSpace c).symm z) * ψ z) := by
  rw [scalarWeightedChartL2_integral]
  calc
    _ = ∫ z, chartVolumeDensity g c z *
        (scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z) *
          scalarChartOperator g c ψ z) := by
      apply integral_congr_ae
      filter_upwards with z
      by_cases hz : z ∈ tsupport ψ
      · rw [hone z hz]
        ring
      · rw [scalarChartOperator_eq_zero_off_tsupport g c ψ hz]
        ring
    _ = ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z) *
          scalarChartOperator g c ψ z) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [scalarChartOperator_eq_zero_off_tsupport g c ψ (fun h => hz (hψt h))]
      ring
    _ = ∫ z in (chartAt FourSpace c).target, chartVolumeDensity g c z *
        (f ((chartAt FourSpace c).symm z) * ψ z) :=
      scalarH1_L2_weak_coordinate_distribution g o d f u hw c ψ hψ hψc hψt
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hψt h))]
      ring

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.reconstruction_baseProbability
theorem scalarChartReconstruction_chartCutoff (g : SmoothMetric M) (c : M)
    (ρ a : SmoothScalar (M := M)) (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    scalarChartReconstruction g c (scalarChartSupport_compact c ρ hs)
      (scalarChartSupport_subset c ρ hs)
      (ScalarEuclideanSobolev.valueL2 (scalarCutoffChartC1 c
        (scalarChartSupport_subset c ρ hs) (scalarChartCutoff c ρ)
        (scalarChartCutoff_smooth c ρ hs) (scalarChartCutoff_compact c ρ hs)
        (scalarChartCutoff_support c ρ hs) a)) =
      smoothScalarBaseL2 g (smoothScalarProduct ρ a) := by
  let K := scalarChartSupport c ρ
  let f := scalarCutoffChartC1 c (scalarChartSupport_subset c ρ hs)
    (scalarChartCutoff c ρ) (scalarChartCutoff_smooth c ρ hs)
    (scalarChartCutoff_compact c ρ hs) (scalarChartCutoff_support c ρ hs) a
  have he : scalarChartReconstructionFun c K f.val = (smoothScalarProduct ρ a).val := by
    funext x
    by_cases hx : x ∈ (chartAt FourSpace c).symm '' K
    · have hxs : x ∈ (chartAt FourSpace c).source := by
        obtain ⟨z, hz, rfl⟩ := hx
        exact (chartAt FourSpace c).map_target (scalarChartSupport_subset c ρ hs hz)
      change ((chartAt FourSpace c).symm '' K).indicator (fun y =>
        scalarChartCutoff c ρ (chartAt FourSpace c y) *
          a.val ((chartAt FourSpace c).symm (chartAt FourSpace c y))) x = ρ.val x * a.val x
      rw [indicator_of_mem hx, scalarChartCutoff_apply c ρ hxs,
        (chartAt FourSpace c).left_inv hxs]
    · have hρ : ρ.val x = 0 := by
        by_contra hn
        have ht := subset_tsupport ρ.val hn
        exact hx ⟨chartAt FourSpace c x, ⟨x, ht, rfl⟩, (chartAt FourSpace c).left_inv (hs ht)⟩
      change ((chartAt FourSpace c).symm '' K).indicator _ x = ρ.val x * a.val x
      rw [indicator_of_notMem hx, hρ, zero_mul]
  have hpoint : scalarChartReconstructionFun c K f.val =ᵐ[normalizedVolume g]
      (smoothScalarProduct ρ a).val := Filter.Eventually.of_forall (congrFun he)
  apply Lp.ext
  exact (scalarChartReconstruction_coe g c (scalarChartSupport_compact c ρ hs)
    (scalarChartSupport_subset c ρ hs) (ScalarEuclideanSobolev.valueL2 f)).trans
      ((scalarChartReconstructionFun_ae g c (scalarChartSupport_compact c ρ hs)
        (scalarChartSupport_subset c ρ hs) (ScalarEuclideanSobolev.valueL2_coe f)).trans
        (hpoint.trans
          (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
            (⟨(smoothScalarProduct ρ a).val,
              (smoothScalarProduct ρ a).property.continuous⟩ : C(M, ℝ))).symm))

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.rescaledL2Tests_frameCompact
theorem scalarRescaled_L2_test_equation (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : Lp ℝ 2 (normalizedVolume g)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarBasePullback g o f)
          (scalarH1Value d v)))
    (c : M) {K : Set FourSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt FourSpace c).target)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ K)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0)
    (ψ : FourSpace → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψt : ∀ y ∈ tsupport ψ,
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target)
    (hone : ∀ y ∈ tsupport ψ, χ (scalarRescaledPoint g c z₀ r y) = 1) :
    (∫ y, scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ r hr) z₀
        (scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs) y *
          scalarRescaledOperator g c z₀ r ψ y) =
      ∫ y, r ^ 2 * chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
        f ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y)) * ψ y := by
  let A := scalarRescalingLinearEquiv g c z₀ r hr
  let ψ₀ : FourSpace → ℝ := fun z => ψ (A.symm (z - z₀))
  have hp : ContDiff ℝ ∞ ψ₀ :=
    hψ.comp (A.symm.contDiff.comp (contDiff_id.sub contDiff_const))
  have hpc : HasCompactSupport ψ₀ := by
    have h := hψc.comp_homeomorph
      ((Homeomorph.addRight (-z₀.val)).trans A.symm.toHomeomorph)
    change HasCompactSupport (fun z => ψ (A.symm (z + -z₀.val))) at h
    simpa only [ψ₀, sub_eq_add_neg] using h
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ r (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ r hr]
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hps {z : FourSpace} (hz : z ∈ tsupport ψ₀) : A.symm (z - z₀) ∈ tsupport ψ :=
    tsupport_comp_subset_preimage (f := fun z => A.symm (z - z₀)) ψ (by fun_prop) hz
  have hpt : tsupport ψ₀ ⊆ (chartAt FourSpace c).target := by
    intro z hz
    have h := hψt _ (hps hz)
    rwa [hinv] at h
  have hpo : ∀ z ∈ tsupport ψ₀, χ z = 1 := by
    intro z hz
    have h := hone _ (hps hz)
    rwa [hinv] at h
  have heq := scalarWeightedChartL2_L2_test_equation g o d f u hw c hK hKt
    χ hχ hc hs ψ₀ hp hpc hpt hpo
  have hop (z : FourSpace) : scalarRescaledOperator g c z₀ r ψ (A.symm (z - z₀)) =
      r ^ 2 * scalarChartOperator g c ψ₀ z := by
    have h := scalarRescaledOperator_eq_chart g c z₀ r hr ψ hψ (A.symm (z - z₀))
    rw [hinv] at h
    exact h.symm
  rw [scalarAffineL2_integral]
  change scalarAffineJacobian A * (∫ z, _ * scalarRescaledOperator g c z₀ r ψ
    (A.symm (z - z₀))) = _
  simp_rw [hop]
  have hmul : (∫ z, scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs z *
      (r ^ 2 * scalarChartOperator g c ψ₀ z)) =
      r ^ 2 * ∫ z, scalarWeightedChartL2 g o d c hK hKt u χ hχ hc hs z *
        scalarChartOperator g c ψ₀ z := by
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  rw [hmul, heq]
  have hsource := scalarAffine_integral A z₀.val (fun z =>
    chartVolumeDensity g c z * (f ((chartAt FourSpace c).symm z) * ψ₀ z))
  have htest (y : FourSpace) : ψ₀ (A y + z₀) = ψ y := by
    simp only [ψ₀, add_sub_cancel_right, A.symm_apply_apply]
  change (∫ y, chartVolumeDensity g c (A y + z₀) *
    (f ((chartAt FourSpace c).symm (A y + z₀)) * ψ₀ (A y + z₀))) = _ at hsource
  have hpoint (y : FourSpace) : A y + z₀ = scalarRescaledPoint g c z₀ r y :=
    scalarRescalingLinearEquiv_apply g c z₀ r hr y
  have htest' (y : FourSpace) : ψ₀ (scalarRescaledPoint g c z₀ r y) = ψ y := by
    rw [← hpoint, htest]
  simp only [hpoint, htest'] at hsource
  rw [mul_left_comm (scalarAffineJacobian A) (r ^ 2), ← hsource,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.rellichCompactness_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.rellichCompactness_probability
def scalarH1ReconstructedPiece (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    (ρ : SmoothScalar (M := M)) (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    scalarH1 d →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (scalarChartReconstruction g c (scalarChartSupport_compact c ρ hs)
    (scalarChartSupport_subset c ρ hs)).comp
      (scalarH1CutoffValueL2 g o d c (scalarChartSupport_compact c ρ hs)
        (scalarChartSupport_subset c ρ hs) (scalarChartCutoff c ρ)
        (scalarChartCutoff_smooth c ρ hs) (scalarChartCutoff_compact c ρ hs)
        (scalarChartCutoff_support c ρ hs))

theorem scalarH1ReconstructedPiece_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    (ρ a : SmoothScalar (M := M)) (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    scalarH1ReconstructedPiece g o d c ρ hs (smoothScalarToH1 d a) =
      smoothScalarBaseL2 g (smoothScalarProduct ρ a) := by
  unfold scalarH1ReconstructedPiece
  rw [ContinuousLinearMap.comp_apply, scalarH1CutoffValueL2_smooth]
  exact scalarChartReconstruction_chartCutoff g c ρ a hs

theorem scalarH1ReconstructedPiece_compact (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
    (ρ : SmoothScalar (M := M)) (hs : tsupport ρ.val ⊆ (chartAt FourSpace c).source) :
    IsCompactOperator (scalarH1ReconstructedPiece g o d c ρ hs) :=
  (scalarH1CutoffValueL2_compact g o d c (scalarChartSupport_compact c ρ hs)
    (scalarChartSupport_subset c ρ hs) (scalarChartCutoff c ρ)
    (scalarChartCutoff_smooth c ρ hs) (scalarChartCutoff_compact c ρ hs)
    (scalarChartCutoff_support c ρ hs)).clm_comp
      (scalarChartReconstruction g c (scalarChartSupport_compact c ρ hs)
        (scalarChartSupport_subset c ρ hs))

theorem scalarH1BaseValue_partition (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (P : ScalarPartition M) :
    scalarH1BaseValue g o d = ∑ i : P.ι, scalarH1ReconstructedPiece g o d (P.center i)
      (scalarPartitionFunction P i) (scalarPartitionFunction_support P i) := by
  apply DFunLike.ext'
  apply (scalarH1BaseValue g o d).continuous.ext_on (smoothScalarH1Map_dense o d)
    (map_continuous _)
  rintro _ ⟨a, rfl⟩
  change scalarH1BaseValue g o d (smoothScalarToH1 d a) =
    (∑ i : P.ι, scalarH1ReconstructedPiece g o d (P.center i)
      (scalarPartitionFunction P i) (scalarPartitionFunction_support P i)) (smoothScalarToH1 d a)
  simp only [scalarH1BaseValue_smooth, sum_apply, scalarH1ReconstructedPiece_smooth]
  change smoothScalarBaseL2Linear g a =
    ∑ i : P.ι, smoothScalarBaseL2Linear g
      (smoothScalarProduct (scalarPartitionFunction P i) a)
  rw [← map_sum, smoothScalar_partition]

/-- The actual inclusion of scalar H¹ into base L² is compact. -/
theorem scalarH1BaseValue_compact (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    IsCompactOperator (scalarH1BaseValue g o d) := by
  obtain ⟨P⟩ := scalarPartition_exists (M := M)
  rw [scalarH1BaseValue_partition g o d P]
  exact (compactOperator (RingHom.id ℝ) (scalarH1 d)
    (Lp ℝ 2 (normalizedVolume g))).sum_mem
    (fun i _ => scalarH1ReconstructedPiece_compact g o d (P.center i)
      (scalarPartitionFunction P i) (scalarPartitionFunction_support P i))

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
theorem scalarBaseResolvent_compact : IsCompactOperator (scalarBaseResolvent g o d) :=
  (scalarH1BaseValue_compact g o d).comp_clm (scalarBaseShiftedSolution g o d)

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (ht : tsupport χ ⊆ (chartAt FourSpace c).target)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.eigenSource_compact
theorem scalarChartSourceL2_baseValue (u : scalarH1 d) :
    scalarChartSourceL2 g c (scalarH1BaseValue g o d u) χ hχ hc ht =
      scalarWeightedChartL2 g o d c hc ht u χ hχ hc (Subset.refl _) := by
  apply Lp.ext
  exact (scalarChartSourceL2_coe g c (scalarH1BaseValue g o d u) χ hχ hc ht).trans
    (scalarWeightedChartL2_coe g o d c hc ht u χ hχ hc (Subset.refl _)).symm

theorem scalarWeightedChartL2_smul (κ : ℝ) (u : scalarH1 d) :
    scalarWeightedChartL2 g o d c hc ht (κ • u) χ hχ hc (Subset.refl _) =
      κ • scalarWeightedChartL2 g o d c hc ht u χ hχ hc (Subset.refl _) := by
  let P := scalarLocalL2ProductCLM hc.measurableSet
    (fun z => χ z * chartVolumeDensity g c z)
    (scalarDensityCutoff_smooth g c χ hχ ht).continuous hc.mul_right
    (tsupport_mul_subset_left.trans (Subset.refl _))
  change P (scalarH1ChartValue g o d c hc ht (κ • u)) =
    κ • P (scalarH1ChartValue g o d c hc ht u)
  rw [map_smul, map_smul]

theorem scalarRescaledEigenSource (κ : ℝ) (u : scalarH1 d)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) :
    scalarRescaledSourceL2 g c (scalarH1BaseValue g o d (κ • u)) χ hχ hc ht z₀ r hr =
      (r ^ 2 * κ) • scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ r hr) z₀
        (scalarWeightedChartL2 g o d c hc ht u χ hχ hc (Subset.refl _)) := by
  rw [scalarRescaledSourceL2, scalarChartSourceL2_baseValue,
    scalarWeightedChartL2_smul]
  exact (congrArg (r ^ 2 • ·) (scalarAffinePullbackL2_smul _ _ κ _)).trans
    (smul_smul (r ^ 2) κ _)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Local smoothness of the actual intrinsic weak Poisson solution.
All coefficients, cutoffs, affine maps and right-hand sides are constructed. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

local notation "V" => FourSpace
local notation "T" => 𝓢'(V, ℂ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localPoisson_frameCompact
theorem scalar_local_weighted_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : SmoothScalar (M := M)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
          (scalarH1Value d v))) (c : M) (z₀ : ChartTarget c) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ closedBall (0 : V) 1,
        scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) ∧
      ∃ F : V → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
          scalarH1BaseValue g o d u
            ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
              volume.restrict (ball (0 : V) (1 / 4))] F := by
  obtain ⟨χ, hχ, hc, ht, η₁, hη₁, hchart⟩ := exists_scalar_chart_cutoff g c z₀
  obtain ⟨η₂, hη₂, hcoeff⟩ := scalarRescaledAdjointSchwartz_small g c z₀
    scalarCoefficientBump scalarCoefficientBump.contDiff scalarCoefficientBump.hasCompactSupport
  let r := min η₁ η₂ / 2
  have hr : 0 < r := half_pos (lt_min hη₁ hη₂)
  have hr₁ : |r| < η₁ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_left _ _)
  have hr₂ : |r| < η₂ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_right _ _)
  obtain ⟨a, b, ha, hb, ha₀, ha₁, ha₂, hb₀, hb₁⟩ := hcoeff r hr₂
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let w₀ := scalarWeightedChartL2 g o d c hc ht u χ hχ hc (Subset.refl _)
  let w := scalarAffinePullbackL2 A z₀ w₀
  have hW : MemSobolev 1 2 (scalarComplexL2 w : T) :=
    scalarAffinePullbackL2_memSobolev_one A z₀ w₀
      (scalarWeightedChartL2_memSobolev_one g o d c hc ht u χ hχ hc (Subset.refl _))
  have htarget (y : V) (hy : y ∈ ball (0 : V) 1) :
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target :=
    (hchart r hr₁ y (ball_subset_closedBall hy)).1
  have hA (y : V) (hy : y ∈ ball (0 : V) 1) (i j : Fin 4) : a i j y =
      ((-((2 * Real.pi) ^ 2)⁻¹ *
        (scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j) : ℝ) : ℂ) := by
    have h := ha i j y
    simpa only [scalarCutoffPrincipal, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  have hB (y : V) (hy : y ∈ ball (0 : V) 1) (i : Fin 4) : b i y =
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledDrift g c z₀ r y i : ℝ) : ℂ) := by
    have h := hb i y
    simpa only [scalarCutoffDrift, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  have hreal (ψ : V → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ ball (0 : V) 1) :
      (∫ y, w y * scalarRescaledOperator g c z₀ r ψ y) =
        ∫ y, scalarRescaledSource g c z₀ r f y * ψ y := by
    exact scalarRescaled_test_equation g o d f u hw c hc ht χ hχ hc (Subset.refl _)
      z₀ r hr.ne' ψ hψ hψc
      (fun y hy => htarget y (hψs hy))
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)
  obtain ⟨F, hF, heq⟩ := scalar_rescaled_solution_smooth g c z₀ r f w hW
    a b htarget hA hB ha₀ ha₁ ha₂ hb₀ hb₁ hreal
  refine ⟨r, hr, fun y hy => (hchart r hr₁ y hy).1, F, hF, ?_⟩
  have hmp : Measure.QuasiMeasurePreserving (fun y : V => A y + z₀) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    rw [scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  have hbase := hmp.ae_eq_comp (scalarWeightedChartL2_coe g o d c hc ht u χ hχ hc (Subset.refl _))
  have hwr := scalarAffinePullbackL2_coe A z₀ w₀
  filter_upwards [heq, ae_restrict_of_ae hbase, ae_restrict_of_ae hwr,
    ae_restrict_mem isOpen_ball.measurableSet] with y hFq hbq hwq hy
  have hy₁ : y ∈ closedBall (0 : V) 1 := by
    apply ball_subset_closedBall
    exact ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1) hy
  have hp := scalarRescalingLinearEquiv_apply g c z₀ r hr.ne' y
  dsimp only [Function.comp_apply] at hbq
  change w₀ (A y + z₀) = _ at hbq
  rw [hp, (hchart r hr₁ y hy₁).2, one_mul] at hbq
  change w y = w₀ (A y + z₀) at hwq
  rw [hp] at hwq
  exact (hwq.trans hbq).symm.trans hFq

end
end PositiveEinsteinFour.Geometry
end


section

/-! Undo the positive chart density and the invertible affine rescaling
in the local smooth representative of the actual Poisson solution. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.unweighting_frameCompact
theorem scalar_local_chart_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : SmoothScalar (M := M)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
          (scalarH1Value d v))) (c : M) (z₀ : ChartTarget c) :
    ∃ U : Set FourSpace, IsOpen U ∧ z₀.val ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
      ∃ F : FourSpace → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        (fun z => scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z)) =ᵐ[
          volume.restrict U] F := by
  obtain ⟨r, hr, ht, F, hF, heq⟩ := scalar_local_weighted_smooth g o d f u hw c z₀
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let U : Set FourSpace := {z | A.symm (z - z₀) ∈ ball (0 : FourSpace) (1 / 4)}
  have hU : IsOpen U := isOpen_ball.preimage (by fun_prop)
  have hz₀ : z₀.val ∈ U := by
    simp only [U, mem_ofPred_eq, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ r (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ r hr.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hUt : U ⊆ (chartAt FourSpace c).target := by
    intro z hz
    have hy : A.symm (z - z₀) ∈ closedBall (0 : FourSpace) 1 :=
      ball_subset_closedBall (ball_subset_ball (by norm_num : (1 / 4 : ℝ) ≤ 1) hz)
    have h := ht _ hy
    rwa [hinv] at h
  let H : FourSpace → ℝ := fun z => F (A.symm (z - z₀)) / chartVolumeDensity g c z
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H U := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    exact ((hF.contDiffAt).comp z
      (A.symm.contDiff.contDiffAt.comp z (contDiffAt_id.sub contDiffAt_const))).div
      (chartVolumeDensity_contDiffAt g c z (hUt hz))
      (chartVolumeDensity_pos g c z (hUt hz)).ne'
  refine ⟨U, hU, hz₀, hUt, H, hH, ?_⟩
  have hmp : Measure.QuasiMeasurePreserving
      (fun z : FourSpace => A.symm (z - z₀)) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    have hfun : (fun z : FourSpace => A.symm (z - z₀)) =
        (fun z => A.symm z + (-A.symm z₀)) := by
      funext z
      rw [map_sub, sub_eq_add_neg]
    rw [hfun, scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  have hglob := hmp.ae ((ae_restrict_iff' isOpen_ball.measurableSet).mp heq)
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hglob] with z hz
  intro hzU
  have he := hz hzU
  rw [hinv] at he
  apply (eq_div_iff (chartVolumeDensity_pos g c z (hUt hzU)).ne').mpr
  simpa only [mul_comm] using he

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

local instance baseEigenbasis_frameCompact_r33aabd_1 (g : SmoothMetric M) :
    CompactSpace (FrameBundle g) := actual_compactFrameBundle g
instance scalarBaseSpectralSpaceFinite (μ : ScalarBaseSpectralValue g o d) :
    FiniteDimensional ℝ (ScalarBaseSpectralSpace g o d μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (scalarBaseResolvent_compact g o d) μ.val
    (scalarBaseResolvent_eigenvalue g o d μ.property).1.ne'

omit [SecondCountableTopology M] in
theorem scalarBaseSpectral_total :
    (⨆ μ : ScalarBaseSpectralValue g o d, ScalarBaseSpectralSpace g o d μ).topologicalClosure = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure]
  change (⨆ μ : {μ // Module.End.eigenspace (scalarBaseResolvent g o d).toLinearMap μ ≠ ⊥},
    Module.End.eigenspace (scalarBaseResolvent g o d).toLinearMap μ.val)ᗮ = ⊥
  rw [iSup_ne_bot_subtype]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (scalarBaseResolvent_compact g o d) (scalarBaseResolvent_symmetric g o d)

def scalarBaseEigenvector (i : ScalarBaseEigenIndex g o d) : Lp ℝ 2 (normalizedVolume g) :=
  (stdOrthonormalBasis ℝ (ScalarBaseSpectralSpace g o d i.1) i.2).val

theorem scalarBaseEigenvector_orthonormal : Orthonormal ℝ (scalarBaseEigenvector g o d) :=
  scalar_spectral_family_orthonormal (scalarBaseResolvent g o d)
    (scalarBaseResolvent_symmetric g o d)

theorem scalarBaseEigenvector_span :
    Submodule.span ℝ (Set.range (scalarBaseEigenvector g o d)) =
      ⨆ μ : ScalarBaseSpectralValue g o d, ScalarBaseSpectralSpace g o d μ := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact (le_iSup (fun μ => ScalarBaseSpectralSpace g o d μ) i.1)
      (stdOrthonormalBasis ℝ (ScalarBaseSpectralSpace g o d i.1) i.2).property
  · apply iSup_le
    intro μ x hx
    let b := stdOrthonormalBasis ℝ (ScalarBaseSpectralSpace g o d μ)
    have he := congrArg (ScalarBaseSpectralSpace g o d μ).subtype
      (b.sum_repr (⟨x, hx⟩ : ScalarBaseSpectralSpace g o d μ))
    simp only [map_sum, map_smul] at he
    change (∑ j, (b.repr ⟨x, hx⟩) j • (b j : Lp ℝ 2 (normalizedVolume g))) = x at he
    rw [← he]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨⟨μ, j⟩, rfl⟩

def scalarBaseEigenbasis : HilbertBasis (ScalarBaseEigenIndex g o d) ℝ
    (Lp ℝ 2 (normalizedVolume g)) :=
  HilbertBasis.mk (scalarBaseEigenvector_orthonormal g o d) (by
    rw [scalarBaseEigenvector_span, scalarBaseSpectral_total])

theorem scalarBaseEigenvector_hasEigenvector (i : ScalarBaseEigenIndex g o d) :
    Module.End.HasEigenvector (scalarBaseResolvent g o d).toLinearMap i.1.val
      (scalarBaseEigenvector g o d i) := by
  refine ⟨(stdOrthonormalBasis ℝ (ScalarBaseSpectralSpace g o d i.1) i.2).property, ?_⟩
  have hn := (scalarBaseEigenvector_orthonormal g o d).1 i
  intro h
  rw [h, norm_zero] at hn
  exact zero_ne_one hn

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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o)) (c : M)
  (χ : FourSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
  (ht : tsupport χ ⊆ (chartAt FourSpace c).target)

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.iteratedSource_compact
theorem scalarWeightedChartL2_sub (u v : scalarH1 d) :
    scalarWeightedChartL2 g o d c hc ht (u - v) χ hχ hc (Subset.refl _) =
      scalarWeightedChartL2 g o d c hc ht u χ hχ hc (Subset.refl _) -
        scalarWeightedChartL2 g o d c hc ht v χ hχ hc (Subset.refl _) := by
  let P := scalarLocalL2ProductCLM hc.measurableSet
    (fun z => χ z * chartVolumeDensity g c z)
    (scalarDensityCutoff_smooth g c χ hχ ht).continuous hc.mul_right
    (tsupport_mul_subset_left.trans (Subset.refl _))
  change P (scalarH1ChartValue g o d c hc ht (u - v)) =
    P (scalarH1ChartValue g o d c hc ht u) - P (scalarH1ChartValue g o d c hc ht v)
  rw [map_sub, map_sub]

theorem scalarRescaledDifferenceSource (u v : scalarH1 d)
    (z₀ : ChartTarget c) (r : ℝ) (hr : r ≠ 0) :
    scalarRescaledSourceL2 g c (scalarH1BaseValue g o d (u - v)) χ hχ hc ht z₀ r hr =
      r ^ 2 • (scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ r hr) z₀
        (scalarWeightedChartL2 g o d c hc ht u χ hχ hc (Subset.refl _)) -
      scalarAffinePullbackL2 (scalarRescalingLinearEquiv g c z₀ r hr) z₀
        (scalarWeightedChartL2 g o d c hc ht v χ hχ hc (Subset.refl _))) := by
  rw [scalarRescaledSourceL2, scalarChartSourceL2_baseValue,
    scalarWeightedChartL2_sub, scalarAffinePullbackL2_sub]

end
end PositiveEinsteinFour.Geometry
end


section

/-! All integer local regularity for actual scalar weak eigenfunctions.
The eigenvalue becomes a compact zeroth-order coefficient; no regularity premise is added. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localEigenRegularity_frameCompact
theorem scalar_eigen_local_all_orders (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (κ : ℝ)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        κ * inner ℝ (scalarH1BaseValue g o d u) (scalarH1BaseValue g o d v)) (c : M) (z₀ : ChartTarget c) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ closedBall (0 : V) 1,
        scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) ∧
      ∃ w : Lp ℝ 2 (volume : Measure V),
        (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
          scalarH1BaseValue g o d u
            ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
              volume.restrict (ball (0 : V) 1)] w ∧
        ∀ (n : ℕ) (φ : S), HasCompactSupport (φ : V → ℂ) →
          tsupport (φ : V → ℂ) ⊆ closedBall 0 (1 / 2) →
          MemSobolev (n : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2 w : T)) := by
  let f := scalarH1BaseValue g o d (-κ • u)
  have hwp : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarBasePullback g o f) (scalarH1Value d v)) := by
    intro v
    dsimp only [f]
    rw [scalarH1BaseValue_spec, map_smul, real_inner_smul_left]
    have hi := (scalarBasePullback g o).inner_map_map (scalarH1BaseValue g o d u)
      (scalarH1BaseValue g o d v)
    rw [scalarH1BaseValue_spec, scalarH1BaseValue_spec] at hi
    rw [hi]
    simpa only [neg_mul, neg_neg] using hw v
  obtain ⟨χ, hχ, hc, ht, η₁, hη₁, hchart⟩ := exists_scalar_chart_cutoff g c z₀
  obtain ⟨η₂, hη₂, hcoeff⟩ := scalarRescaledAdjointSchwartz_small g c z₀
    scalarCoefficientBump scalarCoefficientBump.contDiff scalarCoefficientBump.hasCompactSupport
  let r := min η₁ η₂ / 2
  have hr : 0 < r := half_pos (lt_min hη₁ hη₂)
  have hr₁ : |r| < η₁ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_left _ _)
  have hr₂ : |r| < η₂ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_right _ _)
  obtain ⟨a, b, ha, hb, ha₀, ha₁, ha₂, hb₀, hb₁⟩ := hcoeff r hr₂
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let w₀ := scalarWeightedChartL2 g o d c hc ht u χ hχ hc (Subset.refl _)
  let w := scalarAffinePullbackL2 A z₀ w₀
  have hW : MemSobolev 1 2 (scalarComplexL2 w : T) :=
    scalarAffinePullbackL2_memSobolev_one A z₀ w₀
      (scalarWeightedChartL2_memSobolev_one g o d c hc ht u χ hχ hc (Subset.refl _))
  have htarget (y : V) (hy : y ∈ ball (0 : V) 1) :
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target :=
    (hchart r hr₁ y (ball_subset_closedBall hy)).1
  have hA (y : V) (hy : y ∈ ball (0 : V) 1) (i j : Fin 4) : a i j y =
      ((-((2 * Real.pi) ^ 2)⁻¹ *
        (scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j) : ℝ) : ℂ) := by
    have h := ha i j y
    simpa only [scalarCutoffPrincipal, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  have hB (y : V) (hy : y ∈ ball (0 : V) 1) (i : Fin 4) : b i y =
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledDrift g c z₀ r y i : ℝ) : ℂ) := by
    have h := hb i y
    simpa only [scalarCutoffDrift, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  let F := scalarRescaledSourceL2 g c f χ hχ hc ht z₀ r hr.ne'
  have hreal (ψ : V → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ ball (0 : V) 1) :
      (∫ y, w y * scalarRescaledOperator g c z₀ r ψ y) = ∫ y, F y * ψ y := by
    rw [scalarRescaled_L2_test_equation g o d f u hwp c hc ht χ hχ hc (Subset.refl _)
      z₀ r hr.ne' ψ hψ hψc (fun y hy => htarget y (hψs hy))
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)]
    exact (scalarRescaledSourceL2_pairing g c f χ hχ hc ht z₀ r hr.ne' ψ
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)).symm
  have htests (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
      (hφs : tsupport (φ : V → ℂ) ⊆ ball 0 1) :
      (scalarPerturbedOperator a (scalarAdjointDrift a b) (scalarComplexL2 w : T) -
          (scalarComplexL2 w : T) - smulLeftCLM ℂ (-scalarAdjointPotential a b : S)
            (scalarComplexL2 w : T)) φ =
        ∫ y, φ y * ((-((2 * Real.pi) ^ 2)⁻¹ * F y : ℝ) : ℂ) := by
    rw [scalarFormalAdjointOperator_remainder]
    exact scalar_normalized_adjoint_test_equation_of_integrable g c z₀ r F w a b
      (ball 0 1) hA hB hreal φ hφc hφs (scalar_real_L2_test_integrable F φ _)
  have hFeq : F = (r ^ 2 * (-κ)) • w :=
    scalarRescaledEigenSource g o d c χ hχ hc ht (-κ) u z₀ r hr.ne'
  let k : ℝ := -((2 * Real.pi) ^ 2)⁻¹ * (r ^ 2 * (-κ))
  have htestEigen (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
      (hφs : tsupport (φ : V → ℂ) ⊆ ball 0 1) :
      (scalarPerturbedOperator a (scalarAdjointDrift a b) (scalarComplexL2 w : T) -
          (scalarComplexL2 w : T) - smulLeftCLM ℂ (-scalarAdjointPotential a b : S)
            (scalarComplexL2 w : T)) φ = (k : ℂ) * (scalarComplexL2 w : T) φ :=
    (htests φ hφc hφs).trans (scalar_eigen_source_pairing w F
      (-((2 * Real.pi) ^ 2)⁻¹) (r ^ 2 * (-κ)) hFeq φ)
  refine ⟨r, hr, fun y hy => (hchart r hr₁ y hy).1, w, ?_, ?_⟩
  ·
    have hmp : Measure.QuasiMeasurePreserving (fun y : V => A y + z₀) volume volume := by
      refine ⟨by fun_prop, ?_⟩
      rw [scalarAffine_map_volume]
      exact Measure.smul_absolutelyContinuous
    have hbase := hmp.ae_eq_comp (scalarWeightedChartL2_coe g o d c hc ht u χ hχ hc (Subset.refl _))
    have hwr := scalarAffinePullbackL2_coe A z₀ w₀
    filter_upwards [ae_restrict_of_ae hbase, ae_restrict_of_ae hwr,
      ae_restrict_mem isOpen_ball.measurableSet] with y hbq hwq hy
    have hy₁ : y ∈ closedBall (0 : V) 1 := ball_subset_closedBall hy
    have hp := scalarRescalingLinearEquiv_apply g c z₀ r hr.ne' y
    dsimp only [Function.comp_apply] at hbq
    change w₀ (A y + z₀) = _ at hbq
    rw [hp, (hchart r hr₁ y hy₁).2, one_mul] at hbq
    change w y = w₀ (A y + z₀) at hwq
    rw [hp] at hwq
    exact (hwq.trans hbq).symm
  · intro n φ hφc hφs
    exact scalar_eigen_all_integer_orders a (scalarAdjointDrift a b)
      scalarEllipticSmallSize scalarEllipticSmallSize_pos.le ha₀ ha₁ ha₂ hb₀ hb₁
      scalarEllipticSmallSize_small (-scalarAdjointPotential a b) (scalarEigenCutoff k)
      (k : ℂ) (scalarEigenCutoff_on_ball k) (scalarComplexL2 w : T) hW htestEigen
      (1 / 2) (by norm_num) (by norm_num) n φ hφc hφs

end
end PositiveEinsteinFour.Geometry
end


section

/-! Global smooth representatives of the actual intrinsic weak Poisson
solutions, obtained from the proved local coordinate regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.poissonRegularity_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.poissonRegularity_probability
theorem scalar_weak_poisson_smooth_representative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (f : SmoothScalar (M := M)) (u : scalarH1 d)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        -(inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) f)
          (scalarH1Value d v))) :
    ∃ F : SmoothScalar (M := M), scalarH1Value d u =
      smoothScalarValueL2 g (canonicalFrameMeasure g o) F := by
  let b := scalarH1BaseValue g o d u
  have hlocal (x : M) : ∃ U : Set M, ∃ F : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I4 𝓘(ℝ, ℝ) ∞ F U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] F := by
    let z₀ : ChartTarget x := ⟨chartAt FourSpace x x,
      (chartAt FourSpace x).map_source (mem_chart_source FourSpace x)⟩
    obtain ⟨U, hU, hxU, _, F, hF, he⟩ := scalar_local_chart_smooth g o d f u hw x z₀
    let W := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' U
    refine ⟨W, fun y => F (chartAt FourSpace x y),
      (chartAt FourSpace x).isOpen_inter_preimage hU, ⟨mem_chart_source FourSpace x, hxU⟩,
      ?_, scalar_chart_representative_ae g x U hU b F he⟩
    intro y hy
    have hFC : ContDiffAt ℝ (⊤ : ℕ∞) F (chartAt FourSpace x y) :=
      (hF _ hy.2).contDiffAt (hU.mem_nhds hy.2)
    exact (hFC.contMDiffAt.comp y
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hy.1)).contMDiffWithinAt
  obtain ⟨F, hF⟩ := scalar_smooth_representative_of_local g b hlocal
  have hb : smoothScalarBaseL2 g F = b := by
    apply Lp.ext
    have hcoe := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (⟨F.val, F.property.continuous⟩ : C(M, ℝ))
    filter_upwards [hcoe, hF] with x hx hFx
    exact hx.trans hFx
  refine ⟨F, ?_⟩
  rw [← scalarH1BaseValue_spec g o d u]
  change scalarBasePullback g o b = _
  rw [← hb, scalarBasePullback_smooth]

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

def scalarBaseSpectralEquiv := (scalarBaseEigenbasis g o d).repr


def scalarBaseSpectralMultiplier
    (a : ScalarBaseEigenIndex g o d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) : Lp ℝ 2 (normalizedVolume g) →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  (scalarBaseSpectralEquiv g o d).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((lp.mapCLM 2
      (fun μ => a μ • ContinuousLinearMap.id ℝ (ℝ))
      hC (fun μ => by
        calc
          ‖a μ • ContinuousLinearMap.id ℝ (ℝ)‖ ≤ |a μ| := by
            apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
            intro v
            change ‖a μ • v‖ ≤ |a μ| * ‖v‖
            rw [norm_smul, Real.norm_eq_abs]
          _ ≤ C := ha μ)).comp
      (scalarBaseSpectralEquiv g o d).toContinuousLinearEquiv.toContinuousLinearMap)

theorem scalarBaseSpectralMultiplier_coordinate
    (a : ScalarBaseEigenIndex g o d → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ μ, |a μ| ≤ C) (f : Lp ℝ 2 (normalizedVolume g)) (μ : ScalarBaseEigenIndex g o d) :
    (scalarBaseSpectralEquiv g o d (scalarBaseSpectralMultiplier g o d a C hC ha f)) μ =
      a μ • (scalarBaseSpectralEquiv g o d f) μ := by
  change ((scalarBaseSpectralEquiv g o d)
    ((scalarBaseSpectralEquiv g o d).symm _)) μ = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Undo the positive chart density and the invertible affine rescaling
in the local smooth representative of the actual scalar weak eigenfunction. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set Metric Filter
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.eigenUnweighting_frameCompact
theorem scalar_eigen_local_chart_smooth (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (κ : ℝ)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        κ * inner ℝ (scalarH1BaseValue g o d u) (scalarH1BaseValue g o d v)) (c : M) (z₀ : ChartTarget c) :
    ∃ U : Set FourSpace, IsOpen U ∧ z₀.val ∈ U ∧ U ⊆ (chartAt FourSpace c).target ∧
      ∃ F : FourSpace → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) F U ∧
        (fun z => scalarH1BaseValue g o d u ((chartAt FourSpace c).symm z)) =ᵐ[
          volume.restrict U] F := by
  obtain ⟨r, hr, ht, w, hw, hreg⟩ := scalar_eigen_local_all_orders g o d u κ hw c z₀
  obtain ⟨F, hF, hFw⟩ := scalar_half_smooth_real_representative w
    (fun n φ hc hs => hreg n φ hc (hs.trans ball_subset_closedBall))
  have hwsmall : (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
      scalarH1BaseValue g o d u ((chartAt FourSpace c).symm
        (scalarRescaledPoint g c z₀ r y))) =ᵐ[
      volume.restrict (ball (0 : FourSpace) (1 / 8))] w :=
    ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by norm_num : (1 / 8 : ℝ) ≤ 1)) hw
  have heq := hwsmall.trans hFw
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  let U : Set FourSpace := {z | A.symm (z - z₀) ∈ ball (0 : FourSpace) (1 / 8)}
  have hU : IsOpen U := isOpen_ball.preimage (by fun_prop)
  have hz₀ : z₀.val ∈ U := by
    simp only [U, mem_ofPred_eq, sub_self, map_zero, mem_ball, dist_self]
    norm_num
  have hinv (z : FourSpace) : scalarRescaledPoint g c z₀ r (A.symm (z - z₀)) = z := by
    rw [← scalarRescalingLinearEquiv_apply g c z₀ r hr.ne']
    change A (A.symm (z - z₀)) + z₀ = z
    rw [A.apply_symm_apply, sub_add_cancel]
  have hUt : U ⊆ (chartAt FourSpace c).target := by
    intro z hz
    have hy : A.symm (z - z₀) ∈ closedBall (0 : FourSpace) 1 :=
      ball_subset_closedBall (ball_subset_ball (by norm_num : (1 / 8 : ℝ) ≤ 1) hz)
    have h := ht _ hy
    rwa [hinv] at h
  let H : FourSpace → ℝ := fun z => F (A.symm (z - z₀)) / chartVolumeDensity g c z
  have hH : ContDiffOn ℝ (⊤ : ℕ∞) H U := by
    intro z hz
    apply ContDiffAt.contDiffWithinAt
    exact ((hF.contDiffAt).comp z
      (A.symm.contDiff.contDiffAt.comp z (contDiffAt_id.sub contDiffAt_const))).div
      (chartVolumeDensity_contDiffAt g c z (hUt hz))
      (chartVolumeDensity_pos g c z (hUt hz)).ne'
  refine ⟨U, hU, hz₀, hUt, H, hH, ?_⟩
  have hmp : Measure.QuasiMeasurePreserving
      (fun z : FourSpace => A.symm (z - z₀)) volume volume := by
    refine ⟨by fun_prop, ?_⟩
    have hfun : (fun z : FourSpace => A.symm (z - z₀)) =
        (fun z => A.symm z + (-A.symm z₀)) := by
      funext z
      rw [map_sub, sub_eq_add_neg]
    rw [hfun, scalarAffine_map_volume]
    exact Measure.smul_absolutelyContinuous
  have hglob := hmp.ae ((ae_restrict_iff' isOpen_ball.measurableSet).mp heq)
  apply (ae_restrict_iff' hU.measurableSet).mpr
  filter_upwards [hglob] with z hz
  intro hzU
  have he := hz hzU
  rw [hinv] at he
  apply (eq_div_iff (chartVolumeDensity_pos g c z (hUt hzU)).ne').mpr
  simpa only [mul_comm] using he

end
end PositiveEinsteinFour.Geometry
end


section

/-! All integer local regularity for actual scalar weak eigenfunctions.
The eigenvalue becomes a compact zeroth-order coefficient; no regularity premise is added. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory TemperedDistribution Set Metric
open scoped Manifold ContDiff SchwartzMap

noncomputable section

local notation "V" => FourSpace
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.localChain_frameCompact
theorem scalar_resolvent_chain_local (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (c : M) (z₀ : ChartTarget c) :
    ∃ r : ℝ, 0 < r ∧
      (∀ y ∈ closedBall (0 : V) 1,
        scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target) ∧
      ∀ (U : ℕ → scalarH1 d),
        (∀ k (v : scalarH1 d),
          (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i (U (k + 1))) (scalarH1Gradient d i v)) =
            inner ℝ (scalarH1BaseValue g o d (U k) - scalarH1BaseValue g o d (U (k + 1)))
              (scalarH1BaseValue g o d v)) →
      ∃ w : ℕ → Lp ℝ 2 (volume : Measure V),
        (∀ k, (fun y => chartVolumeDensity g c (scalarRescaledPoint g c z₀ r y) *
          scalarH1BaseValue g o d (U k)
            ((chartAt FourSpace c).symm (scalarRescaledPoint g c z₀ r y))) =ᵐ[
              volume.restrict (ball (0 : V) 1)] w k) ∧
        ∀ (n : ℕ) (φ : S), HasCompactSupport (φ : V → ℂ) →
          tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2) →
          MemSobolev ((2 * n + 1 : ℕ) : ℝ) 2 (smulLeftCLM ℂ φ (scalarComplexL2 (w n) : T)) := by
  obtain ⟨χ, hχ, hc, ht, η₁, hη₁, hchart⟩ := exists_scalar_chart_cutoff g c z₀
  obtain ⟨η₂, hη₂, hcoeff⟩ := scalarRescaledAdjointSchwartz_small g c z₀
    scalarCoefficientBump scalarCoefficientBump.contDiff scalarCoefficientBump.hasCompactSupport
  let r := min η₁ η₂ / 2
  have hr : 0 < r := half_pos (lt_min hη₁ hη₂)
  have hr₁ : |r| < η₁ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_left _ _)
  have hr₂ : |r| < η₂ := by
    rw [abs_of_pos hr]
    exact (half_lt_self (lt_min hη₁ hη₂)).trans_le (min_le_right _ _)
  obtain ⟨a, b, ha, hb, ha₀, ha₁, ha₂, hb₀, hb₁⟩ := hcoeff r hr₂
  let A := scalarRescalingLinearEquiv g c z₀ r hr.ne'
  refine ⟨r, hr, fun y hy => (hchart r hr₁ y hy).1, ?_⟩
  intro U hw
  let f := fun k => scalarH1BaseValue g o d (U (k + 1) - U k)
  have hwp (k : ℕ) (v : scalarH1 d) :
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i (U (k + 1))) (scalarH1Gradient d i v)) =
        -(inner ℝ (scalarBasePullback g o (f k)) (scalarH1Value d v)) := by
    have hi : inner ℝ (scalarBasePullback g o (f k)) (scalarH1Value d v) =
        inner ℝ (f k) (scalarH1BaseValue g o d v) := by
      rw [← scalarH1BaseValue_spec g o d v]
      exact (scalarBasePullback g o).inner_map_map (f k) (scalarH1BaseValue g o d v)
    rw [hi]
    dsimp only [f]
    rw [map_sub, inner_sub_left]
    have he := hw k v
    rw [inner_sub_left] at he
    linarith only [he]
  let w₀ := fun k => scalarWeightedChartL2 g o d c hc ht (U k) χ hχ hc (Subset.refl _)
  let w := fun k => scalarAffinePullbackL2 A z₀ (w₀ k)
  have hW (k : ℕ) : MemSobolev 1 2 (scalarComplexL2 (w k) : T) :=
    scalarAffinePullbackL2_memSobolev_one A z₀ (w₀ k)
      (scalarWeightedChartL2_memSobolev_one g o d c hc ht (U k) χ hχ hc (Subset.refl _))
  have htarget (y : V) (hy : y ∈ ball (0 : V) 1) :
      scalarRescaledPoint g c z₀ r y ∈ (chartAt FourSpace c).target :=
    (hchart r hr₁ y (ball_subset_closedBall hy)).1
  have hA (y : V) (hy : y ∈ ball (0 : V) 1) (i j : Fin 4) : a i j y =
      ((-((2 * Real.pi) ^ 2)⁻¹ *
        (scalarRescaledPrincipal g c z₀ r y i j - (1 : Mat4) i j) : ℝ) : ℂ) := by
    have h := ha i j y
    simpa only [scalarCutoffPrincipal, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  have hB (y : V) (hy : y ∈ ball (0 : V) 1) (i : Fin 4) : b i y =
      ((-((2 * Real.pi) ^ 2)⁻¹ * scalarRescaledDrift g c z₀ r y i : ℝ) : ℂ) := by
    have h := hb i y
    simpa only [scalarCutoffDrift, scalarCoefficientBump_one (ball_subset_closedBall hy),
      one_mul, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg] using h
  let F := fun k => scalarRescaledSourceL2 g c (f k) χ hχ hc ht z₀ r hr.ne'
  have hreal (k : ℕ) (ψ : V → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
      (hψs : tsupport ψ ⊆ ball (0 : V) 1) :
      (∫ y, w (k + 1) y * scalarRescaledOperator g c z₀ r ψ y) = ∫ y, F k y * ψ y := by
    rw [scalarRescaled_L2_test_equation g o d (f k) (U (k + 1)) (hwp k) c hc ht χ hχ hc (Subset.refl _)
      z₀ r hr.ne' ψ hψ hψc (fun y hy => htarget y (hψs hy))
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)]
    exact (scalarRescaledSourceL2_pairing g c (f k) χ hχ hc ht z₀ r hr.ne' ψ
      (fun y hy => (hchart r hr₁ y (ball_subset_closedBall (hψs hy))).2)).symm
  have htests (k : ℕ) (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
      (hφs : tsupport (φ : V → ℂ) ⊆ ball 0 1) :
      (scalarPerturbedOperator a (scalarAdjointDrift a b) (scalarComplexL2 (w (k + 1)) : T) -
          (scalarComplexL2 (w (k + 1)) : T) - smulLeftCLM ℂ (-scalarAdjointPotential a b : S)
            (scalarComplexL2 (w (k + 1)) : T)) φ =
        ∫ y, φ y * ((-((2 * Real.pi) ^ 2)⁻¹ * F k y : ℝ) : ℂ) := by
    rw [scalarFormalAdjointOperator_remainder]
    exact scalar_normalized_adjoint_test_equation_of_integrable g c z₀ r (F k) (w (k + 1)) a b
      (ball 0 1) hA hB (hreal k) φ hφc hφs (scalar_real_L2_test_integrable (F k) φ _)
  let κ : ℝ := -((2 * Real.pi) ^ 2)⁻¹ * r ^ 2
  have htestChain (k : ℕ) (φ : S) (hφc : HasCompactSupport (φ : V → ℂ))
      (hφs : tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2)) :
      (scalarPerturbedOperator a (scalarAdjointDrift a b) (scalarComplexL2 (w (k + 1)) : T) -
          (scalarComplexL2 (w (k + 1)) : T) -
          smulLeftCLM ℂ (-scalarAdjointPotential a b + scalarEigenCutoff κ : S)
            (scalarComplexL2 (w (k + 1)) : T)) φ =
        -(κ : ℂ) * (scalarComplexL2 (w k) : T) φ := by
    have hφs₁ := hφs.trans (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))
    have hFeq : F k = r ^ 2 • (w (k + 1) - w k) :=
      scalarRescaledDifferenceSource g o d c χ hχ hc ht (U (k + 1)) (U k) z₀ r hr.ne'
    have he := (htests k φ hφc hφs₁).trans (scalar_eigen_source_pairing
      (w (k + 1) - w k) (F k) (-((2 * Real.pi) ^ 2)⁻¹) (r ^ 2) hFeq φ)
    rw [scalarComplexL2_sub_distribution, sub_apply] at he
    rw [scalar_multiplier_add]
    simp only [sub_apply, add_apply] at he ⊢
    rw [scalar_multiplier_constant_on_test (scalarEigenCutoff κ) φ
      (scalarComplexL2 (w (k + 1)) : T) (κ : ℂ)
      (fun x hx => scalarEigenCutoff_on_ball κ x (hφs₁ hx))]
    change _ = (κ : ℂ) * (_ - _) at he
    linear_combination he
  refine ⟨w, ?_, ?_⟩
  · intro k
    have hmp : Measure.QuasiMeasurePreserving (fun y : V => A y + z₀) volume volume := by
      refine ⟨by fun_prop, ?_⟩
      rw [scalarAffine_map_volume]
      exact Measure.smul_absolutelyContinuous
    have hbase := hmp.ae_eq_comp (scalarWeightedChartL2_coe g o d c hc ht (U k) χ hχ hc (Subset.refl _))
    have hwr := scalarAffinePullbackL2_coe A z₀ (w₀ k)
    filter_upwards [ae_restrict_of_ae hbase, ae_restrict_of_ae hwr,
      ae_restrict_mem isOpen_ball.measurableSet] with y hbq hwq hy
    have hy₁ : y ∈ closedBall (0 : V) 1 := ball_subset_closedBall hy
    have hp := scalarRescalingLinearEquiv_apply g c z₀ r hr.ne' y
    dsimp only [Function.comp_apply] at hbq
    change w₀ k (A y + z₀) = _ at hbq
    rw [hp, (hchart r hr₁ y hy₁).2, one_mul] at hbq
    change w k y = w₀ k (A y + z₀) at hwq
    rw [hp] at hwq
    exact (hwq.trans hbq).symm
  · intro n φ hφc hφs
    exact scalar_iterate_open_integer_gain a (scalarAdjointDrift a b)
      scalarEllipticSmallSize scalarEllipticSmallSize_pos.le ha₀ ha₁ ha₂ hb₀ hb₁
      scalarEllipticSmallSize_small (-scalarAdjointPotential a b + scalarEigenCutoff κ)
      (-(κ : ℂ)) (fun k => (scalarComplexL2 (w k) : T)) hW htestChain n φ hφc hφs

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

def scalarBaseHeat (t : ℝ≥0) : Lp ℝ 2 (normalizedVolume g) →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  scalarBaseSpectralMultiplier g o d (scalarBaseHeatWeight g o d t) 1 zero_le_one
    (scalarBaseHeatWeight_bound g o d t)

theorem scalarBaseHeat_coordinate (t : ℝ≥0) (f : Lp ℝ 2 (normalizedVolume g))
    (μ : ScalarBaseEigenIndex g o d) :
    (scalarBaseSpectralEquiv g o d (scalarBaseHeat g o d t f)) μ =
      scalarBaseHeatWeight g o d t μ • (scalarBaseSpectralEquiv g o d f) μ :=
  scalarBaseSpectralMultiplier_coordinate g o d _ _ _ _ f μ

end
end PositiveEinsteinFour.Geometry
end


section

/-! Global smooth representatives of actual intrinsic weak scalar eigenfunctions, obtained from the proved local coordinate regularity. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.eigenSmooth_frameCompact
attribute [local instance] OAI.PositiveEinsteinFour.Geometry.eigenSmooth_probability
theorem scalar_weak_eigen_smooth_representative (g : SmoothMetric M) (o : FrameOrientation g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (u : scalarH1 d) (κ : ℝ)
    (hw : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        κ * inner ℝ (scalarH1BaseValue g o d u) (scalarH1BaseValue g o d v)) :
    ∃ F : SmoothScalar (M := M), scalarH1Value d u =
      smoothScalarValueL2 g (canonicalFrameMeasure g o) F := by
  let b := scalarH1BaseValue g o d u
  have hlocal (x : M) : ∃ U : Set M, ∃ F : M → ℝ,
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn I4 𝓘(ℝ, ℝ) ∞ F U ∧
        (b : M → ℝ) =ᵐ[(normalizedVolume g).restrict U] F := by
    let z₀ : ChartTarget x := ⟨chartAt FourSpace x x,
      (chartAt FourSpace x).map_source (mem_chart_source FourSpace x)⟩
    obtain ⟨U, hU, hxU, _, F, hF, he⟩ := scalar_eigen_local_chart_smooth g o d u κ hw x z₀
    let W := (chartAt FourSpace x).source ∩ (chartAt FourSpace x) ⁻¹' U
    refine ⟨W, fun y => F (chartAt FourSpace x y),
      (chartAt FourSpace x).isOpen_inter_preimage hU, ⟨mem_chart_source FourSpace x, hxU⟩,
      ?_, scalar_chart_representative_ae g x U hU b F he⟩
    intro y hy
    have hFC : ContDiffAt ℝ (⊤ : ℕ∞) F (chartAt FourSpace x y) :=
      (hF _ hy.2).contDiffAt (hU.mem_nhds hy.2)
    exact (hFC.contMDiffAt.comp y
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hy.1)).contMDiffWithinAt
  obtain ⟨F, hF⟩ := scalar_smooth_representative_of_local g b hlocal
  have hb : smoothScalarBaseL2 g F = b := by
    apply Lp.ext
    have hcoe := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (normalizedVolume g)
      (⟨F.val, F.property.continuous⟩ : C(M, ℝ))
    filter_upwards [hcoe, hF] with x hx hFx
    exact hx.trans hFx
  refine ⟨F, ?_⟩
  rw [← scalarH1BaseValue_spec g o d u]
  change scalarBasePullback g o b = _
  rw [← hb, scalarBasePullback_smooth]

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

theorem scalarBaseResolvent_coordinate (f : Lp ℝ 2 (normalizedVolume g))
    (i : ScalarBaseEigenIndex g o d) :
    scalarBaseSpectralEquiv g o d (scalarBaseResolvent g o d f) i =
      i.1.val • scalarBaseSpectralEquiv g o d f i := by
  change (scalarBaseEigenbasis g o d).repr (scalarBaseResolvent g o d f) i =
    i.1.val • (scalarBaseEigenbasis g o d).repr f i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  simp only [scalarBaseEigenbasis, HilbertBasis.coe_mk]
  change inner ℝ (scalarBaseEigenvector g o d i) (scalarBaseResolvent g o d f) =
    i.1.val * inner ℝ (scalarBaseEigenvector g o d i) f
  have he := Module.End.mem_eigenspace_iff.mp
    (scalarBaseEigenvector_hasEigenvector g o d i).1
  change scalarBaseResolvent g o d (scalarBaseEigenvector g o d i) =
    i.1.val • scalarBaseEigenvector g o d i at he
  have hs : inner ℝ (scalarBaseEigenvector g o d i) (scalarBaseResolvent g o d f) =
      inner ℝ (scalarBaseResolvent g o d (scalarBaseEigenvector g o d i)) f :=
    (scalarBaseResolvent_symmetric g o d (scalarBaseEigenvector g o d i) f).symm
  rw [hs, he, real_inner_smul_left]

def scalarBaseHeatPowerSource (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    Lp ℝ 2 (normalizedVolume g) →L[ℝ] Lp ℝ 2 (normalizedVolume g) :=
  scalarBaseSpectralMultiplier g o d (fun μ => μ.1.val⁻¹ ^ n * scalarBaseHeatWeight g o d t μ)
    (Real.exp t * (n.factorial : ℝ) / (t : ℝ) ^ n) (by positivity)
    (scalarBaseHeatPowerWeight_bound g o d t ht n)

theorem scalarBaseResolvent_power_coordinate (n : ℕ) (f : Lp ℝ 2 (normalizedVolume g))
    (μ : ScalarBaseEigenIndex g o d) :
    (scalarBaseSpectralEquiv g o d ((scalarBaseResolvent g o d ^ n) f)) μ =
      μ.1.val ^ n • (scalarBaseSpectralEquiv g o d f) μ := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      change (scalarBaseSpectralEquiv g o d
        ((scalarBaseResolvent g o d ^ n) (scalarBaseResolvent g o d f))) μ = _
      rw [ih, scalarBaseResolvent_coordinate, smul_smul, ← pow_succ]

theorem scalarBaseHeatPowerSource_resolvent (t : ℝ≥0) (ht : 0 < t)
    (n : ℕ) (f : Lp ℝ 2 (normalizedVolume g)) :
    (scalarBaseResolvent g o d ^ n) (scalarBaseHeatPowerSource g o d t ht n f) =
      scalarBaseHeat g o d t f := by
  apply (scalarBaseSpectralEquiv g o d).injective
  apply lp.ext
  funext μ
  rw [scalarBaseResolvent_power_coordinate, scalarBaseHeat_coordinate]
  change μ.1.val ^ n • (scalarBaseSpectralEquiv g o d
    (scalarBaseSpectralMultiplier g o d _ _ _ _ f)) μ = _
  rw [scalarBaseSpectralMultiplier_coordinate, smul_smul]
  congr 1
  have hm : μ.1.val ≠ 0 := (scalarBaseResolvent_eigenvalue g o d μ.1.property).1.ne'
  rw [← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hm, one_pow, one_mul]

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual scalar spectral vectors are smooth functions satisfying the
geometric Laplace eigenvalue equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.eigenPointwise_frameCompact
theorem scalar_weak_eigen_smooth (u : scalarH1 d) (κ : ℝ)
    (hu : ∀ v : scalarH1 d,
      (∑ i : Fin 4, inner ℝ (scalarH1Gradient d i u) (scalarH1Gradient d i v)) =
        κ * inner ℝ (scalarH1BaseValue g o d u) (scalarH1BaseValue g o d v)) :
    ∃ F : SmoothScalar (M := M), u = smoothScalarToH1 d F ∧
      smoothScalarLaplacian g F = (-κ) • F := by
  obtain ⟨F, hF⟩ := scalar_weak_eigen_smooth_representative g o d u κ hu
  have hueq : u = smoothScalarToH1 d F := scalarH1_eq_smooth_of_value d u F hF
  let r : SmoothScalar (M := M) := smoothScalarLaplacian g F + κ • F
  have hr (b : SmoothScalar (M := M)) :
      inner ℝ (smoothScalarValueL2 g (canonicalFrameMeasure g o) r)
        (smoothScalarValueL2 g (canonicalFrameMeasure g o) b) = 0 := by
    have he := hu (smoothScalarToH1 d b)
    rw [hueq] at he
    simp only [scalarH1BaseValue_smooth] at he
    change smoothScalarDirichlet d F b =
      κ * inner ℝ (smoothScalarBaseL2 g F) (smoothScalarBaseL2 g b) at he
    have hi := (scalarBasePullback g o).inner_map_map (smoothScalarBaseL2 g F)
      (smoothScalarBaseL2 g b)
    rw [scalarBasePullback_smooth, scalarBasePullback_smooth] at hi
    rw [← hi, smoothScalarDirichlet_symm d F b,
      smoothScalarDirichlet_laplacian_pairing] at he
    dsimp only [r]
    rw [map_add, map_smul, inner_add_left, real_inner_smul_left,
      smoothScalarLaplacian_valueL2]
    have hc := real_inner_comm (smoothScalarValueL2 g (canonicalFrameMeasure g o) b)
      (smoothScalarLaplacianL2 (μ := canonicalFrameMeasure g o) F)
    linarith only [he, hc]
  have hz : smoothScalarValueL2 g (canonicalFrameMeasure g o) r = 0 :=
    inner_self_eq_zero.mp (hr r)
  have hr0 : r = 0 := smoothScalarValueL2_injective g o (by simpa only [map_zero] using hz)
  refine ⟨F, hueq, ?_⟩
  change smoothScalarLaplacian g F + κ • F = 0 at hr0
  have heq := eq_neg_of_add_eq_zero_left hr0
  ext x
  have hx := congrArg (fun a : SmoothScalar (M := M) => a.val x) heq
  change (smoothScalarLaplacian g F).val x = (-κ) * F.val x
  change (smoothScalarLaplacian g F).val x = -(κ * F.val x) at hx
  simpa only [neg_mul] using hx

variable [SecondCountableTopology M]

theorem scalarBaseEigenvector_smooth (i : ScalarBaseEigenIndex g o d) :
    ∃ F : SmoothScalar (M := M), scalarBaseEigenvector g o d i = smoothScalarBaseL2 g F ∧
      smoothScalarLaplacian g F = (-(i.1.val⁻¹ - 1)) • F := by
  obtain ⟨u, hval, hu⟩ := scalarBaseResolvent_eigenvector_weak g o d
    (scalarBaseEigenvector_hasEigenvector g o d i)
  obtain ⟨F, hF, hL⟩ := scalar_weak_eigen_smooth g o d u (i.1.val⁻¹ - 1) (fun v => by
    rw [hu v, hval])
  refine ⟨F, ?_, hL⟩
  rw [← hval, hF, scalarH1BaseValue_smooth]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Smooth scalar eigenfunctions chosen from the actual orthonormal basis,
with their exact heat evolution and geometric Laplace equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarBaseEigenfunction (i : ScalarBaseEigenIndex g o d) : SmoothScalar (M := M) :=
  (scalarBaseEigenvector_smooth g o d i).choose

theorem scalarBaseEigenfunction_L2 (i : ScalarBaseEigenIndex g o d) :
    scalarBaseEigenvector g o d i = smoothScalarBaseL2 g (scalarBaseEigenfunction g o d i) :=
  (scalarBaseEigenvector_smooth g o d i).choose_spec.1

theorem scalarBaseEigenfunction_laplacian (i : ScalarBaseEigenIndex g o d) :
    smoothScalarLaplacian g (scalarBaseEigenfunction g o d i) =
      (-scalarBaseHeatRate g o d i) • scalarBaseEigenfunction g o d i :=
  (scalarBaseEigenvector_smooth g o d i).choose_spec.2

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
theorem scalarBaseShiftedSolution_eigen_smooth (i : ScalarBaseEigenIndex g o d) :
    scalarBaseShiftedSolution g o d (scalarBaseEigenvector g o d i) =
      i.1.val • smoothScalarToH1 d (scalarBaseEigenfunction g o d i) := by
  apply scalarH1BaseValue_injective g o d
  change scalarBaseResolvent g o d (scalarBaseEigenvector g o d i) = _
  rw [map_smul, scalarH1BaseValue_smooth, ← scalarBaseEigenfunction_L2]
  exact Module.End.mem_eigenspace_iff.mp (scalarBaseEigenvector_hasEigenvector g o d i).1

theorem scalarH1_eigenfunctions_total :
    (Submodule.span ℝ (range (fun i : ScalarBaseEigenIndex g o d =>
      smoothScalarToH1 d (scalarBaseEigenfunction g o d i)))).topologicalClosure = ⊤ := by
  have he := dense_span_continuousLinearMap_image (scalarBaseEigenvector g o d)
    (by rw [scalarBaseEigenvector_span, scalarBaseSpectral_total])
    (scalarBaseShiftedSolution g o d) (scalarBaseShiftedSolution_dense g o d)
  have hs : Submodule.span ℝ (range (fun i =>
      scalarBaseShiftedSolution g o d (scalarBaseEigenvector g o d i))) ≤
      Submodule.span ℝ (range (fun i : ScalarBaseEigenIndex g o d =>
        smoothScalarToH1 d (scalarBaseEigenfunction g o d i))) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change scalarBaseShiftedSolution g o d (scalarBaseEigenvector g o d i) ∈ _
    rw [scalarBaseShiftedSolution_eigen_smooth]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  apply top_unique
  rw [← he]
  exact Submodule.topologicalClosure_mono hs

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
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]

variable (g : SmoothMetric M) (o : FrameOrientation g)
  (d : ParallelMetricData g (canonicalFrameMeasure g o))

def scalarHeatConvolution (R : ℝ → Lp ℝ 2 (normalizedVolume g)) (t : ℝ) : Lp ℝ 2 (normalizedVolume g) :=
  ∫ s in (0 : ℝ)..t, scalarBaseHeat g o d (t - s).toNNReal (R s)

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

def twoFormRoughResolvent : TwoFormL2 o →L[ℝ] TwoFormL2 o :=
  twoFormH1ToL2.comp twoFormRoughSolution

theorem twoFormRoughResolvent_compact : IsCompactOperator (twoFormRoughResolvent (o := o)) :=
  twoFormH1ToL2_compact.comp_clm twoFormRoughSolution

end
end PositiveEinsteinFour.Geometry
end


section

/-! Finite-dimensional weak kernels for the bounded curvature potential
in the two-form Weitzenböck equation. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormPotentialResolvent (B : TwoFormL2 o →L[ℝ] TwoFormL2 o) :
    TwoFormL2 o →L[ℝ] TwoFormL2 o := twoFormRoughResolvent.comp B

theorem twoFormPotentialResolvent_compact (B : TwoFormL2 o →L[ℝ] TwoFormL2 o) :
    IsCompactOperator (twoFormPotentialResolvent B) :=
  twoFormRoughResolvent_compact.comp_clm B

def twoFormWeakPotentialKernel (B : TwoFormL2 o →L[ℝ] TwoFormL2 o) :
    Submodule ℝ (TwoFormH1 o) :=
  (ContinuousLinearMap.id ℝ (TwoFormH1 o) -
    twoFormRoughSolution.comp (B.comp twoFormH1ToL2)).ker

theorem mem_twoFormWeakPotentialKernel (B : TwoFormL2 o →L[ℝ] TwoFormL2 o)
    (u : TwoFormH1 o) : u ∈ twoFormWeakPotentialKernel B ↔
      u = twoFormRoughSolution (B (twoFormH1ToL2 u)) := by
  simp only [twoFormWeakPotentialKernel, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, sub_eq_zero]

theorem twoFormWeakPotentialKernel_weak (B : TwoFormL2 o →L[ℝ] TwoFormL2 o)
    (u : TwoFormH1 o) : u ∈ twoFormWeakPotentialKernel B ↔
      ∀ v, inner ℝ u v = inner ℝ (B (twoFormH1ToL2 u)) (twoFormH1ToL2 v) := by
  rw [mem_twoFormWeakPotentialKernel]
  constructor
  · intro hu v
    conv_lhs => rw [hu]
    exact twoFormRoughSolution_weak _ _
  · exact twoFormRoughSolution_unique _ u

def twoFormPotentialKernelValue (B : TwoFormL2 o →L[ℝ] TwoFormL2 o) :
    twoFormWeakPotentialKernel B →ₗ[ℝ]
      Module.End.eigenspace (twoFormPotentialResolvent B).toLinearMap 1 where
  toFun u := ⟨twoFormH1ToL2 u.val, by
    rw [Module.End.mem_eigenspace_iff]
    change twoFormH1ToL2 (twoFormRoughSolution (B (twoFormH1ToL2 u.val))) =
      (1 : ℝ) • twoFormH1ToL2 u.val
    rw [one_smul, ← (mem_twoFormWeakPotentialKernel B u.val).mp u.property]⟩
  map_add' u v := Subtype.ext (map_add twoFormH1ToL2 u.val v.val)
  map_smul' r u := Subtype.ext (map_smul twoFormH1ToL2 r u.val)

theorem twoFormPotentialKernelValue_injective (B : TwoFormL2 o →L[ℝ] TwoFormL2 o) :
    Function.Injective (twoFormPotentialKernelValue B) := by
  intro u v huv
  have hval : twoFormH1ToL2 u.val = twoFormH1ToL2 v.val := congrArg Subtype.val huv
  apply Subtype.ext
  rw [(mem_twoFormWeakPotentialKernel B u.val).mp u.property,
    (mem_twoFormWeakPotentialKernel B v.val).mp v.property, hval]

theorem twoFormWeakPotentialKernel_finite (B : TwoFormL2 o →L[ℝ] TwoFormL2 o) :
    FiniteDimensional ℝ (twoFormWeakPotentialKernel B) := by
  let _ := ContinuousLinearMap.finite_dimensional_eigenspace
    (twoFormPotentialResolvent_compact B) (1 : ℝ) one_ne_zero
  exact FiniteDimensional.of_injective (twoFormPotentialKernelValue B)
    (twoFormPotentialKernelValue_injective B)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The finite-dimensional weak solution space of the actual curvature
equation, and its positive and negative Hodge summands. Identifying this
space with de Rham harmonic forms uses the exterior differential identities. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

def twoFormWeitzenbockKernel : Submodule ℝ (TwoFormH1 o) :=
  twoFormWeakPotentialKernel twoFormWeitzenbockPotential

instance twoFormWeitzenbockKernel_finite : FiniteDimensional ℝ (twoFormWeitzenbockKernel (o := o)) :=
  twoFormWeakPotentialKernel_finite _

end
end PositiveEinsteinFour.Geometry
end


section

/-! The closed nonnegative Hodge form on the actual H1 completion. Its
zero-energy space is the finite weak harmonic kernel. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormHodgeForm_add_left (u v w : TwoFormH1 o) :
    twoFormHodgeForm (u + v) w = twoFormHodgeForm u w + twoFormHodgeForm v w := by
  simp only [twoFormHodgeForm, map_add, inner_add_left]
  ring

theorem twoFormHodgeForm_add_right (u v w : TwoFormH1 o) :
    twoFormHodgeForm u (v + w) = twoFormHodgeForm u v + twoFormHodgeForm u w := by
  rw [twoFormHodgeForm_comm, twoFormHodgeForm_add_left,
    twoFormHodgeForm_comm v u, twoFormHodgeForm_comm w u]

theorem twoFormHodgeForm_smul_right (r : ℝ) (u v : TwoFormH1 o) :
    twoFormHodgeForm u (r • v) = r * twoFormHodgeForm u v := by
  rw [twoFormHodgeForm_comm, twoFormHodgeForm_smul_left, twoFormHodgeForm_comm v u]

theorem twoFormHodgeForm_zero_left (hRic : RicciThree g) (u : TwoFormH1 o)
    (hu : twoFormHodgeForm u u = 0) (v : TwoFormH1 o) : twoFormHodgeForm u v = 0 := by
  apply linear_term_zero (twoFormHodgeForm_nonneg hRic v)
  intro t
  have h := twoFormHodgeForm_nonneg hRic (u + t • v)
  simp only [twoFormHodgeForm_add_left, twoFormHodgeForm_add_right,
    twoFormHodgeForm_smul_left, twoFormHodgeForm_smul_right, hu,
    twoFormHodgeForm_comm v u] at h
  nlinarith only [h]

theorem mem_twoFormWeitzenbockKernel_iff_energy_zero (hRic : RicciThree g) (u : TwoFormH1 o) :
    u ∈ twoFormWeitzenbockKernel ↔ twoFormHodgeForm u u = 0 := by
  rw [twoFormWeitzenbockKernel, twoFormWeakPotentialKernel_weak]
  constructor
  · intro h
    exact sub_eq_zero.mpr (h u)
  · intro hu v
    exact sub_eq_zero.mp (twoFormHodgeForm_zero_left hRic u hu v)

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

def twoFormHarmonicProjection : TwoFormH1 o →L[ℝ] TwoFormH1 o :=
  (twoFormWeitzenbockKernel (o := o)).starProjection

theorem twoFormHarmonicProjection_compact :
    IsCompactOperator (twoFormHarmonicProjection (o := o)) :=
  (isCompactOperator_of_locallyCompactSpace_rng
    (twoFormWeitzenbockKernel (o := o)).subtypeL).comp_clm
      (twoFormWeitzenbockKernel (o := o)).orthogonalProjectionOnto

theorem twoFormHarmonicProjection_inner (u : TwoFormH1 o) :
    inner ℝ (twoFormHarmonicProjection u) u =
      inner ℝ (twoFormHarmonicProjection u) (twoFormHarmonicProjection u) := by
  have h := Submodule.starProjection_inner_eq_zero (K := twoFormWeitzenbockKernel (o := o))
    u (twoFormHarmonicProjection u)
      (Submodule.starProjection_apply_mem _ u)
  rw [inner_sub_left] at h
  change inner ℝ u (twoFormHarmonicProjection u) -
    inner ℝ (twoFormHarmonicProjection u) (twoFormHarmonicProjection u) = 0 at h
  rw [real_inner_comm (twoFormHarmonicProjection u) u] at h
  exact sub_eq_zero.mp h

def twoFormRegularizedHodge : TwoFormH1 o →L[ℝ] TwoFormH1 o :=
  twoFormHodgeOperator + twoFormHarmonicProjection

theorem twoFormRegularizedHodge_eq_zero (hRic : RicciThree g) (u : TwoFormH1 o)
    (hu : twoFormRegularizedHodge u = 0) : u = 0 := by
  have hinner := congrArg (fun v : TwoFormH1 o => inner ℝ v u) hu
  change inner ℝ (twoFormHodgeOperator u + twoFormHarmonicProjection u) u = inner ℝ 0 u at hinner
  rw [inner_add_left, twoFormHodgeOperator_inner, twoFormHarmonicProjection_inner,
    inner_zero_left] at hinner
  have h0 := twoFormHodgeForm_nonneg hRic u
  have hP := real_inner_self_nonneg (x := twoFormHarmonicProjection u)
  have hE : twoFormHodgeForm u u = 0 := by linarith
  have hK := (mem_twoFormWeitzenbockKernel_iff_energy_zero hRic u).mpr hE
  have hPr : twoFormHarmonicProjection u = u :=
    Submodule.starProjection_eq_self_iff.mpr hK
  have hL : twoFormHodgeOperator u = 0 := hK
  change twoFormHodgeOperator u + twoFormHarmonicProjection u = 0 at hu
  simpa only [hL, hPr, zero_add] using hu

theorem twoFormRegularizedHodge_surjective (hRic : RicciThree g) :
    Function.Surjective (twoFormRegularizedHodge (o := o)) := by
  let T : TwoFormH1 o →L[ℝ] TwoFormH1 o := twoFormHodgeCompact - twoFormHarmonicProjection
  have hc : IsCompactOperator T := twoFormHodgeCompact_compact.sub twoFormHarmonicProjection_compact
  have he : (1 : TwoFormH1 o →L[ℝ] TwoFormH1 o) - T = twoFormRegularizedHodge := by
    apply ContinuousLinearMap.ext
    intro u
    change u - (twoFormHodgeCompact u - twoFormHarmonicProjection u) =
      (u - twoFormHodgeCompact u) + twoFormHarmonicProjection u
    module
  rcases hc.hasEigenvalue_or_mem_resolventSet (one_ne_zero : (1 : ℝ) ≠ 0) with hv | hr
  · obtain ⟨u, hu⟩ := hv.exists_hasEigenvector
    have hf := (Module.End.mem_eigenspace_iff.mp hu.1)
    change T u = (1 : ℝ) • u at hf
    rw [one_smul] at hf
    have hzero : twoFormRegularizedHodge u = 0 := by
      rw [← he]
      change u - T u = 0
      rw [hf, sub_self]
    exact (hu.2 (twoFormRegularizedHodge_eq_zero hRic u hzero)).elim
  · have hi := spectrum.mem_resolventSet_iff.mp hr
    simp only [map_one] at hi
    rw [he] at hi
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp hi).2

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates07
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite
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

theorem smoothHodgeLaplacian_selfAdjoint (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) v =
      smoothTwoFormL2Inner u (smoothHodgeLaplacian hRic v) := by
  rw [smoothTwoFormL2Inner_comm u, smoothHodgeLaplacian_pairing,
    smoothHodgeLaplacian_pairing, twoFormHodgeForm_comm]

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


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

theorem twoFormWeakHarmonic_rough (u : TwoFormH1 o)
    (hu : u ∈ twoFormWeitzenbockKernel (o := o)) :
    u = twoFormRoughSolution (twoFormWeitzenbockPotential (twoFormH1ToL2 u)) := by
  apply twoFormRoughSolution_unique
  exact (twoFormWeakPotentialKernel_weak _ _).mp hu

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

/-! The eigenvalue one of the actual shifted resolvent is exactly the
smooth harmonic space. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem twoFormShiftedSolution_unique (hRic : RicciThree g) (f : TwoFormL2 o)
    (u : TwoFormH1 o)
    (hu : ∀ v, twoFormHodgeForm u v + inner ℝ (twoFormH1ToL2 u) (twoFormH1ToL2 v) =
      inner ℝ f (twoFormH1ToL2 v)) : u = twoFormShiftedSolution hRic f := by
  apply twoFormShiftedHodge_injective hRic
  apply ext_inner_right ℝ
  intro v
  rw [twoFormShiftedHodge_inner, twoFormShiftedHodge_inner]
  exact (hu v).trans (twoFormShiftedSolution_weak hRic f v).symm

end
end PositiveEinsteinFour.Geometry
end


section

/-! Linearity of the smooth geometric Hodge Laplacian, proved using its
nondegenerate integral pairing. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHodgeLaplacian_add (hRic : RicciThree g) (u v : smoothTwoForms o) :
    smoothHodgeLaplacian hRic (u + v) =
      smoothHodgeLaplacian hRic u + smoothHodgeLaplacian hRic v := by
  apply smoothTwoForm_eq_of_pairings
  intro w
  have he : smoothTwoFormToH1 ((u + v : smoothTwoForms o) : SmoothH1TwoForm o) =
      smoothTwoFormToH1 (u : SmoothH1TwoForm o) +
        smoothTwoFormToH1 (v : SmoothH1TwoForm o) :=
    map_add smoothTwoFormToH1 (u : SmoothH1TwoForm o) (v : SmoothH1TwoForm o)
  rw [smoothTwoFormL2Inner_add, smoothHodgeLaplacian_pairing,
    smoothHodgeLaplacian_pairing, smoothHodgeLaplacian_pairing]
  exact (congrArg (fun t : TwoFormH1 o =>
    twoFormHodgeForm t (smoothTwoFormToH1 (w : SmoothH1TwoForm o))) he).trans
      (twoFormHodgeForm_add_left _ _ _)

theorem smoothHodgeLaplacian_smul (hRic : RicciThree g) (r : ℝ) (u : smoothTwoForms o) :
    smoothHodgeLaplacian hRic (r • u) = r • smoothHodgeLaplacian hRic u := by
  apply smoothTwoForm_eq_of_pairings
  intro w
  have he : smoothTwoFormToH1 ((r • u : smoothTwoForms o) : SmoothH1TwoForm o) =
      r • smoothTwoFormToH1 (u : SmoothH1TwoForm o) :=
    map_smul smoothTwoFormToH1 r (u : SmoothH1TwoForm o)
  rw [smoothTwoFormL2Inner_smul, smoothHodgeLaplacian_pairing,
    smoothHodgeLaplacian_pairing]
  exact (congrArg (fun t : TwoFormH1 o =>
    twoFormHodgeForm t (smoothTwoFormToH1 (w : SmoothH1TwoForm o))) he).trans
      (twoFormHodgeForm_smul_left _ _ _)

def smoothHodgeLaplacianLinear (hRic : RicciThree g) :
    smoothTwoForms o →ₗ[ℝ] smoothTwoForms o where
  toFun := smoothHodgeLaplacian hRic
  map_add' := smoothHodgeLaplacian_add hRic
  map_smul' := smoothHodgeLaplacian_smul hRic

end
end PositiveEinsteinFour.Geometry
end


section

/-! The densely defined L2 generator agrees with the actual smooth
Hodge Laplacian, not merely with a formal spectral expression. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHodgeLaplacian_weak (hRic : RicciThree g) (u : smoothTwoForms o)
    (v : TwoFormH1 o) :
    twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) v =
      inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
        (twoFormH1ToL2 v) := by
  have hc : Continuous (fun w : TwoFormH1 o =>
      twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) w) :=
    (continuous_const.inner continuous_id).sub
      (continuous_const.inner twoFormH1ToL2.continuous)
  have hd : Continuous (fun w : TwoFormH1 o =>
      inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
        (twoFormH1ToL2 w)) := continuous_const.inner twoFormH1ToL2.continuous
  have he : (fun w : TwoFormH1 o =>
      twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) w) =
      (fun w => inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
        (twoFormH1ToL2 w)) := by
    apply (smoothTwoFormToH1_dense (o := o)).equalizer hc hd
    funext w
    change twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o))
      (smoothTwoFormToH1 w) =
      inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
        (twoFormH1ToL2 (smoothTwoFormToH1 w))
    calc
      _ = smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) w :=
        (smoothHodgeLaplacian_pairing hRic u w).symm
      _ = inner ℝ (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o))
          (smoothTwoFormToL2 (w : SmoothL2TwoForm o)) :=
        (smoothTwoFormToL2.inner_map_map
          (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o) (w : SmoothL2TwoForm o)).symm
      _ = _ := congrArg (fun z => inner ℝ
        (smoothTwoFormToL2 (smoothHodgeLaplacian hRic u : SmoothL2TwoForm o)) z)
          (twoFormH1ToL2_smooth w).symm
  exact congrFun he v

end
end PositiveEinsteinFour.Geometry
end


section

/-! The geometric Hodge Laplacian splits as dδ + *dδ*. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothHodgeLaplacian_codiff_self (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) u =
      twoFormCodiffPairing u u +
        twoFormCodiffPairing (smoothTwoFormHodge o u) (smoothTwoFormHodge o u) :=
  (smoothHodgeLaplacian_pairing hRic u u).trans
    ((twoFormHodgeForm_smooth hRic (u : SmoothH1TwoForm o)).trans
      (smoothTwoFormDeRhamEnergy_codiff u))

theorem smoothHodgeLaplacian_codiff_pairing (hRic : RicciThree g)
    (u v : smoothTwoForms o) :
    smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) v =
      twoFormCodiffPairing u v +
        twoFormCodiffPairing (smoothTwoFormHodge o u) (smoothTwoFormHodge o v) := by
  have h := smoothHodgeLaplacian_codiff_self hRic (u + v)
  have hu := smoothHodgeLaplacian_codiff_self hRic u
  have hv := smoothHodgeLaplacian_codiff_self hRic v
  simp only [smoothHodgeLaplacian_add, smoothTwoFormL2Inner_add,
    smoothTwoFormL2Inner_add_right, map_add, twoFormCodiffPairing_add_left,
    twoFormCodiffPairing_add_right] at h
  have hs : smoothTwoFormL2Inner (smoothHodgeLaplacian hRic v) u =
      smoothTwoFormL2Inner (smoothHodgeLaplacian hRic u) v :=
    (smoothHodgeLaplacian_selfAdjoint hRic v u).trans (smoothTwoFormL2Inner_comm _ _)
  rw [hs, twoFormCodiffPairing_comm v u,
    twoFormCodiffPairing_comm (smoothTwoFormHodge o v) (smoothTwoFormHodge o u)] at h
  linarith only [h, hu, hv]

theorem smoothHodgeLaplacian_dDelta_hodge (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothHodgeLaplacian hRic u = smoothTwoFormDDelta u +
      smoothTwoFormHodge o (smoothTwoFormDDelta (smoothTwoFormHodge o u)) := by
  apply smoothTwoForm_eq_of_pairings
  intro v
  rw [smoothTwoFormL2Inner_add, smoothTwoFormL2Inner_hodge_left,
    smoothTwoFormDDelta_pairing hRic, smoothTwoFormDDelta_pairing hRic,
    smoothHodgeLaplacian_codiff_pairing hRic]

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

def twoFormEigenform (hRic : RicciThree g) (i : TwoFormEigenIndex (o := o) hRic) :
    smoothTwoForms o := (twoFormEigenvector_smooth hRic i).choose

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

theorem smoothHodgeLaplacian_of_closed (hRic : RicciThree g) (u : smoothTwoForms o)
    (hu : smoothTwoFormExterior u = 0) :
    smoothHodgeLaplacian hRic u = smoothTwoFormDDelta u := by
  have hz := (smoothTwoForm_closed_iff_codifferential_hodge u).mp hu
  rw [smoothHodgeLaplacian_dDelta_hodge hRic]
  have hw : smoothTwoFormDDelta (smoothTwoFormHodge o u) = 0 := by
    change smoothOneFormExterior (smoothTwoFormCodifferentialField (smoothTwoFormHodge o u)) = 0
    rw [hz]
    exact (smoothOneFormExteriorLinear (o := o)).map_zero
  rw [hw, map_zero, add_zero]

theorem smoothHodgeLaplacian_exterior (hRic : RicciThree g) (u : smoothCovariantFields M 1) :
    smoothHodgeLaplacian hRic (smoothOneFormExterior (o := o) u) =
      smoothOneFormExterior (o := o) (smoothOneFormHodgeLaplacian (o := o) u) := by
  rw [smoothHodgeLaplacian_of_closed hRic _ (smoothOneFormExterior_closed hRic u),
    smoothOneFormHodgeLaplacian_apply]
  change smoothOneFormExteriorLinear _ = smoothOneFormExteriorLinear (_ - _)
  rw [map_sub]
  change smoothOneFormExterior (smoothTwoFormCodifferentialField (smoothOneFormExterior u)) =
    smoothOneFormExterior (smoothTwoFormCodifferentialField (smoothOneFormExterior u)) -
      smoothOneFormExterior (smoothScalarDifferential g (smoothOneFormDivergence g u))
  rw [smoothScalarDifferential_closed, sub_zero]

theorem smoothOneFormHodgeLaplacian_codifferential (hRic : RicciThree g) (u : smoothTwoForms o) :
    smoothOneFormHodgeLaplacian (o := o) (smoothTwoFormCodifferentialField u) =
      smoothTwoFormCodifferentialField (smoothHodgeLaplacian hRic u) := by
  apply smoothOneForm_eq_of_pairings (o := o)
  intro v
  rw [smoothOneFormHodgeLaplacian_selfAdjoint hRic,
    smoothTwoFormCodifferential_pairing hRic, smoothTwoFormCodifferential_pairing hRic,
    ← smoothHodgeLaplacian_exterior hRic, smoothHodgeLaplacian_selfAdjoint hRic]

variable [SecondCountableTopology M]

theorem scalarEigen_differential_is_oneFormEigen
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) (i : ScalarBaseEigenIndex g o d) :
    smoothOneFormHodgeLaplacian (o := o)
        (smoothScalarDifferential g (scalarBaseEigenfunction g o d i)) =
      scalarBaseHeatRate g o d i • smoothScalarDifferential g (scalarBaseEigenfunction g o d i) := by
  rw [smoothOneFormHodgeLaplacian_differential, scalarBaseEigenfunction_laplacian,
    smoothScalarDifferential_smul]
  module

end
end PositiveEinsteinFour.Geometry
end


section

/-! Derivatives of the actual scalar and two-form eigenfamilies are total
in the one-form L2 completion. No spectral completeness is assumed in degree one. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_14
def oneFormDerivedFamily (hRic : RicciThree g)
    (d : ParallelMetricData g (canonicalFrameMeasure g o)) :
    ScalarBaseEigenIndex g o d ⊕ TwoFormEigenIndex (o := o) hRic → OneFormL2 o
  | .inl i => smoothOneFormToL2 ⟨smoothScalarDifferential g (scalarBaseEigenfunction g o d i)⟩
  | .inr i => smoothOneFormToL2 ⟨smoothTwoFormCodifferentialField (twoFormEigenform hRic i)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual smooth Hodge eigenspace is linearly equivalent to its
finite-dimensional resolvent eigenspace. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

theorem smoothTwoForm_resolvent_eigen (hRic : RicciThree g) (μ κ : ℝ)
    (hμκ : μ * (κ + 1) = 1) (u : smoothTwoForms o)
    (hu : smoothHodgeLaplacian hRic u = κ • u) :
    twoFormShiftedResolvent hRic (smoothTwoFormToL2 (u : SmoothL2TwoForm o)) =
      μ • smoothTwoFormToL2 (u : SmoothL2TwoForm o) := by
  have hJ : twoFormH1ToL2 (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) =
      smoothTwoFormToL2 (u : SmoothL2TwoForm o) := twoFormH1ToL2_smooth (u : SmoothH1TwoForm o)
  have hq (v : TwoFormH1 o) :
      twoFormHodgeForm (smoothTwoFormToH1 (u : SmoothH1TwoForm o)) v =
        κ * inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o)) (twoFormH1ToL2 v) := by
    rw [smoothHodgeLaplacian_weak hRic, hu]
    calc
      _ = inner ℝ (κ • smoothTwoFormToL2 (u : SmoothL2TwoForm o)) (twoFormH1ToL2 v) :=
        congrArg (fun z : TwoFormL2 o => inner ℝ z (twoFormH1ToL2 v))
          (smoothTwoFormToL2.map_smul κ (u : SmoothL2TwoForm o))
      _ = _ := by rw [real_inner_smul_left]
  have hs : μ • smoothTwoFormToH1 (u : SmoothH1TwoForm o) =
      twoFormShiftedSolution hRic (smoothTwoFormToL2 (u : SmoothL2TwoForm o)) := by
    apply twoFormShiftedSolution_unique hRic
    intro v
    rw [twoFormHodgeForm_smul_left, map_smul, hJ,
      real_inner_smul_left, hq]
    calc
      _ = (μ * (κ + 1)) * inner ℝ (smoothTwoFormToL2 (u : SmoothL2TwoForm o))
          (twoFormH1ToL2 v) := by ring
      _ = _ := by rw [hμκ, one_mul]
  change twoFormH1ToL2 (twoFormShiftedSolution hRic _) = _
  rw [← hs, map_smul]
  exact congrArg (μ • ·) hJ

def TwoFormSmoothEigenSpace (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :=
  Module.End.eigenspace (smoothHodgeLaplacianLinear (o := o) hRic) (μ.val⁻¹ - 1)

def twoFormSmoothEigenL2 (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :
    TwoFormSmoothEigenSpace hRic μ →ₗ[ℝ] TwoFormSpectralSpace hRic μ where
  toFun u := ⟨smoothTwoFormToL2 (u.val : SmoothL2TwoForm o), by
    apply Module.End.mem_eigenspace_iff.mpr
    apply smoothTwoForm_resolvent_eigen hRic μ.val (μ.val⁻¹ - 1) _ u.val
      (Module.End.mem_eigenspace_iff.mp u.property)
    have hne := ne_of_gt (twoFormSpectralValue_bounds hRic μ).1
    field_simp
    ring⟩
  map_add' u v := Subtype.ext (smoothTwoFormToL2.map_add
    (u.val : SmoothL2TwoForm o) (v.val : SmoothL2TwoForm o))
  map_smul' r u := Subtype.ext (smoothTwoFormToL2.map_smul r (u.val : SmoothL2TwoForm o))

theorem twoFormSmoothEigenL2_injective (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    Function.Injective (twoFormSmoothEigenL2 hRic μ) := by
  intro u v h
  exact Subtype.ext (smoothTwoFormToL2_injective (congrArg Subtype.val h))

instance twoFormSmoothEigenFinite (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    FiniteDimensional ℝ (TwoFormSmoothEigenSpace hRic μ) :=
  FiniteDimensional.of_injective (twoFormSmoothEigenL2 hRic μ)
    (twoFormSmoothEigenL2_injective hRic μ)

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

def oneFormCodiffEigenMap (hRic : RicciThree g) (μ : TwoFormSpectralValue (o := o) hRic) :
    TwoFormSmoothEigenSpace hRic μ →ₗ[ℝ] OneFormL2 o :=
  smoothOneFormL2Linear.comp
    (smoothTwoFormCodifferentialLinear.comp (TwoFormSmoothEigenSpace hRic μ).subtype)

def OneFormCoexactSpectralSpace (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) : Submodule ℝ (OneFormL2 o) :=
  (oneFormCodiffEigenMap hRic μ).range

instance oneFormCoexactSpectralFinite (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) :
    FiniteDimensional ℝ (OneFormCoexactSpectralSpace hRic μ) := by
  let : FiniteDimensional ℝ (TwoFormSmoothEigenSpace hRic μ) := twoFormSmoothEigenFinite hRic μ
  exact Module.Finite.range (oneFormCodiffEigenMap hRic μ)

theorem oneFormCoexactSpectral_representation (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (v : OneFormCoexactSpectralSpace hRic μ) :
    ∃ u : smoothTwoForms o,
      smoothHodgeLaplacian hRic u = (μ.val⁻¹ - 1) • u ∧
      v.val = smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u) := by
  obtain ⟨u, hu⟩ := v.property
  exact ⟨u.val, Module.End.mem_eigenspace_iff.mp u.property, hu.symm⟩

theorem smoothCodiff_eigen (hRic : RicciThree g) (u : smoothTwoForms o) (κ : ℝ)
    (hu : smoothHodgeLaplacian hRic u = κ • u) :
    smoothOneFormHodgeLaplacian (o := o) (smoothTwoFormCodifferentialField u) =
      κ • smoothTwoFormCodifferentialField u := by
  rw [smoothOneFormHodgeLaplacian_codifferential hRic, hu]
  exact (smoothTwoFormCodifferentialLinear (o := o)).map_smul κ u

theorem oneFormCoexactSpectral_orthogonal (hRic : RicciThree g)
    (μ ν : TwoFormSpectralValue (o := o) hRic) (hμν : μ ≠ ν)
    (u : OneFormCoexactSpectralSpace hRic μ) (v : OneFormCoexactSpectralSpace hRic ν) :
    inner ℝ u.val v.val = 0 := by
  obtain ⟨a, ha, hua⟩ := oneFormCoexactSpectral_representation hRic μ u
  obtain ⟨b, hb, hvb⟩ := oneFormCoexactSpectral_representation hRic ν v
  rw [hua, hvb]
  apply smoothOneForm_eigen_orthogonal hRic _ _ _ _
    (smoothCodiff_eigen hRic a _ ha) (smoothCodiff_eigen hRic b _ hb)
  intro he
  apply hμν
  apply Subtype.ext
  apply inv_injective
  exact sub_left_injective he

end
end PositiveEinsteinFour.Geometry
end


section

/-! Orthonormal bases of the actual finite coexact one-form eigenspaces. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] {g : SmoothMetric M} {o : FrameOrientation g}

abbrev OneFormCoexactEigenIndex (hRic : RicciThree g) :=
  Σ μ : TwoFormSpectralValue (o := o) hRic,
    Fin (Module.finrank ℝ (OneFormCoexactSpectralSpace hRic μ))

def oneFormCoexactEigenvector (hRic : RicciThree g) (i : OneFormCoexactEigenIndex (o := o) hRic) :
    OneFormL2 o := (stdOrthonormalBasis ℝ (OneFormCoexactSpectralSpace hRic i.1) i.2).val

theorem oneFormCoexactEigenvector_orthonormal (hRic : RicciThree g) :
    Orthonormal ℝ (oneFormCoexactEigenvector (o := o) hRic) := by
  have hO : OrthogonalFamily (E := OneFormL2 o) ℝ
      (fun μ : TwoFormSpectralValue (o := o) hRic => OneFormCoexactSpectralSpace (o := o) hRic μ)
      (fun μ => (OneFormCoexactSpectralSpace (o := o) hRic μ).subtypeₗᵢ) := by
    intro μ ν hμν u v
    exact oneFormCoexactSpectral_orthogonal hRic μ ν hμν u v
  exact hO.orthonormal_sigma_orthonormal
    (fun μ => (stdOrthonormalBasis ℝ (OneFormCoexactSpectralSpace hRic μ)).orthonormal)

theorem oneFormCoexact_mem_span (hRic : RicciThree g)
    (μ : TwoFormSpectralValue (o := o) hRic) (u : OneFormCoexactSpectralSpace hRic μ) :
    u.val ∈ Submodule.span ℝ (Set.range (oneFormCoexactEigenvector (o := o) hRic)) := by
  let b := stdOrthonormalBasis ℝ (OneFormCoexactSpectralSpace hRic μ)
  have he := congrArg (OneFormCoexactSpectralSpace hRic μ).subtype (b.sum_repr u)
  simp only [map_sum, map_smul] at he
  change (∑ j, (b.repr u) j • (b j : OneFormL2 o)) = u.val at he
  rw [← he]
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨⟨μ, j⟩, rfl⟩

theorem oneFormCoexactEigenvector_smooth (hRic : RicciThree g)
    (i : OneFormCoexactEigenIndex (o := o) hRic) :
    ∃ u : smoothTwoForms o,
      oneFormCoexactEigenvector hRic i =
        smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u) ∧
      smoothOneFormHodgeLaplacian (o := o) (smoothTwoFormCodifferentialField u) =
        (i.1.val⁻¹ - 1) • smoothTwoFormCodifferentialField u := by
  obtain ⟨u, hu, he⟩ := oneFormCoexactSpectral_representation hRic i.1
    (stdOrthonormalBasis ℝ (OneFormCoexactSpectralSpace hRic i.1) i.2)
  exact ⟨u, he, smoothCodiff_eigen hRic u _ hu⟩

theorem oneFormCoexactEigenvector_rate_pos (hRic : RicciThree g)
    (i : OneFormCoexactEigenIndex (o := o) hRic) : 0 < i.1.val⁻¹ - 1 := by
  have hn : 0 ≤ i.1.val⁻¹ - 1 := sub_nonneg.mpr
    ((one_le_inv₀ (twoFormSpectralValue_bounds hRic i.1).1).mpr
      (twoFormSpectralValue_bounds hRic i.1).2)
  by_contra hp
  have hz : i.1.val⁻¹ - 1 = 0 := le_antisymm (le_of_not_gt hp) hn
  obtain ⟨u, he, hu⟩ := oneFormCoexactEigenvector_smooth hRic i
  rw [hz, zero_smul] at hu
  have hu0 := smoothOneFormHodgeLaplacian_eq_zero hRic _ hu
  have he0 : oneFormCoexactEigenvector hRic i = 0 := by rw [he, hu0, map_zero]
  have hnorm := (oneFormCoexactEigenvector_orthonormal hRic).1 i
  rw [he0, norm_zero] at hnorm
  exact zero_ne_one hnorm

end
end PositiveEinsteinFour.Geometry
end


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

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.instCompactSpaceFrameBundle_15
theorem scalarEigen_differential_inner (i j : ScalarBaseEigenIndex g o d) :
    inner ℝ (smoothOneFormL2Linear (o := o)
      (smoothScalarDifferential g (scalarBaseEigenfunction g o d i)))
      (smoothOneFormL2Linear (o := o)
        (smoothScalarDifferential g (scalarBaseEigenfunction g o d j))) =
      scalarBaseHeatRate g o d j *
        inner ℝ (scalarBaseEigenvector g o d i) (scalarBaseEigenvector g o d j) := by
  rw [smoothOneFormL2Linear_inner, smoothScalarDifferential_dirichlet d,
    smoothScalarDirichlet_laplacian_pairing,
    ← smoothScalarLaplacian_valueL2, scalarBaseEigenfunction_laplacian,
    map_smul, real_inner_smul_right]
  have hinner : inner ℝ
      (smoothScalarValueL2 g (canonicalFrameMeasure g o) (scalarBaseEigenfunction g o d i))
      (smoothScalarValueL2 g (canonicalFrameMeasure g o) (scalarBaseEigenfunction g o d j)) =
      inner ℝ (scalarBaseEigenvector g o d i) (scalarBaseEigenvector g o d j) := by
    rw [scalarBaseEigenfunction_L2, scalarBaseEigenfunction_L2]
    rw [← scalarBasePullback_smooth g o (scalarBaseEigenfunction g o d i),
      ← scalarBasePullback_smooth g o (scalarBaseEigenfunction g o d j)]
    exact (scalarBasePullback g o).inner_map_map _ _
  rw [hinner]
  ring

def oneFormExactEigenvector (i : OneFormExactEigenIndex g o d) : OneFormL2 o :=
  (Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ •
    smoothOneFormL2Linear (o := o)
      (smoothScalarDifferential g (scalarBaseEigenfunction g o d i.val))

theorem oneFormExactEigenvector_orthonormal : Orthonormal ℝ (oneFormExactEigenvector g o d) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  simp only [oneFormExactEigenvector, real_inner_smul_left, real_inner_smul_right,
    scalarEigen_differential_inner,
    orthonormal_iff_ite.mp (scalarBaseEigenvector_orthonormal g o d)]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, if_true]
    have hs : (Real.sqrt (scalarBaseHeatRate g o d i.val)) ^ 2 =
        scalarBaseHeatRate g o d i.val := Real.sq_sqrt i.property.le
    have hn : Real.sqrt (scalarBaseHeatRate g o d i.val) ≠ 0 :=
      (Real.sqrt_pos.mpr i.property).ne'
    field_simp
    nlinarith only [hs]
  · have hval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    simp only [hij, hval, ite_false, if_false, mul_zero]

end
end PositiveEinsteinFour.Geometry
end


section

/-! A complete orthonormal one-form eigenfamily, obtained from the actual
scalar and two-form spectra and the proved geometric Hodge decomposition. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

abbrev OneFormEigenIndex := OneFormExactEigenIndex g o d ⊕ OneFormCoexactEigenIndex (o := o) hRic

def oneFormEigenvector : OneFormEigenIndex hRic d → OneFormL2 o :=
  Sum.elim (oneFormExactEigenvector g o d) (oneFormCoexactEigenvector hRic)

omit [PreconnectedSpace M] in
theorem oneForm_exact_coexact_eigen_orthogonal
    (i : OneFormExactEigenIndex g o d) (j : OneFormCoexactEigenIndex (o := o) hRic) :
    inner ℝ (oneFormExactEigenvector g o d i) (oneFormCoexactEigenvector hRic j) = 0 := by
  obtain ⟨u, hu, _⟩ := oneFormCoexactEigenvector_smooth hRic j
  rw [hu]
  change inner ℝ ((Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹ • _)
    (smoothOneFormL2Linear (o := o) (smoothTwoFormCodifferentialField u)) = 0
  rw [real_inner_smul_left, oneForm_exact_coexact_orthogonal hRic, mul_zero]

omit [PreconnectedSpace M] in
theorem oneFormEigenvector_orthonormal : Orthonormal ℝ (oneFormEigenvector hRic d) := by
  constructor
  · intro i
    cases i with
    | inl i => exact (oneFormExactEigenvector_orthonormal g o d).1 i
    | inr i => exact (oneFormCoexactEigenvector_orthonormal hRic).1 i
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        exact (oneFormExactEigenvector_orthonormal g o d).2
          (fun h => hij (congrArg Sum.inl h))
      | inr j => exact oneForm_exact_coexact_eigen_orthogonal hRic d i j
    | inr i =>
      cases j with
      | inl j =>
        rw [real_inner_comm]
        exact oneForm_exact_coexact_eigen_orthogonal hRic d j i
      | inr j =>
        exact (oneFormCoexactEigenvector_orthonormal hRic).2
          (fun h => hij (congrArg Sum.inr h))

end
end PositiveEinsteinFour.Geometry
end


section

/-! Every vector in the completed one-form basis is an actual smooth
geometric eigenform, with a strictly positive Laplace eigenvalue. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

def oneFormHeatRate : OneFormEigenIndex hRic d → ℝ
  | .inl i => scalarBaseHeatRate g o d i.val
  | .inr i => i.1.val⁻¹ - 1

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormHeatRate_pos (i : OneFormEigenIndex hRic d) : 0 < oneFormHeatRate hRic d i := by
  cases i with
  | inl i => exact i.property
  | inr i => exact oneFormCoexactEigenvector_rate_pos hRic i

omit [PreconnectedSpace M] in
theorem oneFormEigenvector_smooth (i : OneFormEigenIndex hRic d) :
    ∃ u : smoothCovariantFields M 1,
      oneFormEigenvector hRic d i = smoothOneFormL2Linear (o := o) u ∧
      smoothOneFormHodgeLaplacian (o := o) u = oneFormHeatRate hRic d i • u := by
  cases i with
  | inl i =>
    let c := (Real.sqrt (scalarBaseHeatRate g o d i.val))⁻¹
    let u := smoothScalarDifferential g (scalarBaseEigenfunction g o d i.val)
    refine ⟨c • u, (smoothOneFormL2Linear.map_smul c u).symm, ?_⟩
    change smoothOneFormHodgeLaplacian (o := o) (c • u) = scalarBaseHeatRate g o d i.val • (c • u)
    rw [map_smul, scalarEigen_differential_is_oneFormEigen]
    exact smul_comm _ _ _
  | inr i =>
    obtain ⟨u, hu, hL⟩ := oneFormCoexactEigenvector_smooth hRic i
    exact ⟨smoothTwoFormCodifferentialField u, hu, hL⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual one-form heat semigroup, defined from the complete smooth
Hodge eigenbasis. Positivity of the spectrum comes from positive Ricci curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Filter
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormHeatRate_nonneg (i : OneFormEigenIndex hRic d) :
    0 ≤ oneFormHeatRate hRic d i := (oneFormHeatRate_pos hRic d i).le

def oneFormHeatWeight (t : ℝ≥0)
    (μ : OneFormEigenIndex hRic d) : ℝ :=
  Real.exp (-(t : ℝ) * oneFormHeatRate hRic d μ)

omit [SecondCountableTopology M] [PreconnectedSpace M] in
theorem oneFormHeatWeight_bound (t : ℝ≥0)
    (μ : OneFormEigenIndex hRic d) : |oneFormHeatWeight hRic d t μ| ≤ 1 := by
  rw [oneFormHeatWeight, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr t.coe_nonneg)
    (oneFormHeatRate_nonneg hRic d μ)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Genuine L2 Riesz columns for one-form heat evaluation in an orthonormal frame. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff NNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

variable (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))

local instance instCompactSpaceFrameBundle_26_r33aabd_1 : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
def oneFormEigenSection (i : OneFormEigenIndex hRic d) : smoothCovariantFields M 1 :=
  (oneFormEigenvector_smooth hRic d i).choose

omit [PreconnectedSpace M] in
theorem oneFormEigenSection_L2 (i : OneFormEigenIndex hRic d) :
    smoothOneFormL2Linear (o := o) (oneFormEigenSection hRic d i) = oneFormEigenvector hRic d i :=
  (oneFormEigenvector_smooth hRic d i).choose_spec.1.symm

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

theorem heatNormalOneGlobalColumn_weak_deriv (E : HeatNormalOneExtension D)
    (C : OpenPartialHomeomorph FourSpace M)
    (hE : EqOn C (frameExponential g o e) C.source)
    (hCt : C.target ⊆ (chartAt FourSpace c).source)
    (hP : ContDiffOn ℝ 2 D.point C.source) (hD : C.source ⊆ Metric.ball 0 D.radius)
    (χ : FourSpace → ℝ) (hχ : ContDiff ℝ 4 χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ C.source) (t : ℝ) (ht : 0 < t) (l : Fin 4)
    (v : smoothCovariantFields M 1) :
    HasDerivAt (fun s => inner ℝ (heatNormalOneGlobalColumn E C hCt hP hD χ hχ hc hs s l)
        (smoothOneFormL2Linear v))
      (inner ℝ (heatNormalOneGlobalTimeColumn E C hCt hP hD χ (hχ.of_le (by norm_num)) hc hs t l)
        (smoothOneFormL2Linear v)) t := by
  let f := fun k x => frameExponentialJacobian g o e x *
    heatNormalOneValue c D.point v x k
  have hV : ContinuousOn (heatNormalOneValue c D.point v)
      C.source := by
    intro x hx
    have hv : ContDiffAt ℝ 2 (heatNormalOneValue c D.point v) x := by
      apply (contDiffAt_piLp (p := 2)).mpr
      intro k
      exact heatNormalOneFormValue_regular 2 c D.point v x
        (hP.contDiffAt (C.open_source.mem_nhds hx)) (D.in_chart x (hD hx)) k
    exact hv.continuousAt.continuousWithinAt
  have hf (k : Fin 4) : ContinuousOn (f k) C.source :=
    (frameExponentialJacobian_continuous g o e).continuousOn.mul
      ((EuclideanSpace.proj k).continuous.comp_continuousOn hV)
  have hχf (k : Fin 4) : Continuous (fun x => χ x * f k x) :=
    heat_continuous_mul_of_tsupport_subset hχ.continuous C.open_source (hf k) hs
  have hd := (HasDerivAt.sum (u := Finset.univ) fun k _ =>
    heatNormalOneCutoffParametrix_pairing_deriv E χ (f k) (hχf k) hc t ht k l).const_mul
      (normalizedChartFactor g).toReal
  have hfun : (fun s => inner ℝ (heatNormalOneGlobalColumn E C hCt hP hD χ hχ hc hs s l)
      (smoothOneFormL2Linear v)) = fun s => (normalizedChartFactor g).toReal *
        ∑ k : Fin 4, ∫ x, heatNormalOneCutoffParametrix E χ s x k l * f k x := by
    funext s
    exact heatNormalOneAmplitudeL2_pairing_sum C hE hCt hP hD (heatNormalOneCutoffColumn E χ s l)
      ((heatNormalOneCutoffColumn_regular E χ hχ s l).of_le (by norm_num))
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneCutoffColumn_support E χ s l))
      ((heatNormalOneCutoffColumn_support E χ s l).trans hs) v
  have hval : inner ℝ (heatNormalOneGlobalTimeColumn E C hCt hP hD χ (hχ.of_le (by norm_num)) hc hs t l)
      (smoothOneFormL2Linear v) = (normalizedChartFactor g).toReal *
        ∑ k : Fin 4, ∫ x, deriv (fun s => heatNormalOneCutoffParametrix E χ s x k l) t * f k x := by
    have hpair := heatNormalOneAmplitudeL2_pairing_sum C hE hCt hP hD (heatNormalOneTimeColumn E χ t l)
      (heatNormalOneTimeColumn_regular E χ (hχ.of_le (by norm_num)) t l)
      (hc.of_isClosed_subset (isClosed_tsupport _) (heatNormalOneTimeColumn_support E χ t l))
      ((heatNormalOneTimeColumn_support E χ t l).trans hs) v
    exact hpair.trans (congrArg ((normalizedChartFactor g).toReal * ·)
      (Finset.sum_congr rfl fun k _ => integral_congr_ae (Eventually.of_forall fun x =>
        congrArg (· * f k x) (heatNormalOneTimeColumn_component E χ t ht l k x))))
  simp only [Finset.sum_apply] at hd
  rw [← hfun, ← hval] at hd
  exact hd

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

theorem HeatNormalParametrixData.oneWeakEvolution
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (t : ℝ) (ht : 0 < t) (l : Fin 4) (v : smoothCovariantFields M 1) :
    HasDerivAt (fun s => inner ℝ (P.oneColumn E s l) (smoothOneFormL2Linear v))
      (inner ℝ (P.oneResidual E t l) (smoothOneFormL2Linear v) -
        inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v))) t := by
  have hd := heatNormalOneGlobalColumn_weak_deriv E P.chart P.exponential
    P.in_chart P.point_regular P.inside_radius P.cutoff P.cutoff_regular
    P.cutoff_compact P.cutoff_support t ht l v
  have hr : inner ℝ (P.oneResidual E t l) (smoothOneFormL2Linear v) -
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
      inner ℝ (P.oneTimeColumn E t l) (smoothOneFormL2Linear v) := by
    rw [HeatNormalParametrixData.oneResidual, inner_add_left, hpair]
    ring
  rw [hr]
  exact hd

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual normal one-form parametrix tends to the correctly normalized delta. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Matrix Set Filter MeasureTheory
open scoped BigOperators Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]

theorem heatNormalOneCutoffParametrix_initial_local {g : SmoothMetric M}
    {o : FrameOrientation g} {c : M} {e : FrameBundle g}
    {D : HeatNormalFrameData g o c e} (E : HeatNormalOneExtension D)
    (χ f : FourSpace → ℝ) (hχf : Continuous (fun x => χ x * f x))
    (hχc : HasCompactSupport χ) (hχ0 : χ 0 = 1) (k l : Fin 4) :
    Tendsto (fun t => ∫ x, heatNormalOneCutoffParametrix E χ t x k l * f x)
      (𝓝[Ioi 0] 0) (𝓝 ((if k = l then 1 else 0) * f 0)) := by
  let u : Fin 4 → FourSpace → ℝ := fun m x => (χ x * f x) * E.amplitude m x k l
  have hu (m : Fin 4) : Continuous (u m) :=
    hχf.mul (E.amplitude_regular m (by omega) k l).continuous
  have huc (m : Fin 4) : HasCompactSupport (u m) := (hχc.mul_right).mul_right
  have hb (m : Fin 4) : ∃ C : ℝ, ∀ x, ‖u m x‖ ≤ C := by
    obtain ⟨C, hC⟩ := ((huc m).isCompact_range (hu m)).bddAbove_image
      continuous_norm.continuousOn
    exact ⟨C, fun x => hC (mem_image_of_mem _ (mem_range_self x))⟩
  choose C hC using hb
  have h := fourHeatPolynomial_approximate_identity u hu C hC
  have hU : E.base.U 0 = 1 :=
    E.base.U_near.self_of_nhds.trans (heatNormalLeadingAmplitude_zero g o e)
  have hzero : u 0 0 = (if k = l then 1 else 0) * f 0 := by
    change (χ 0 * f 0) * E.amplitude 0 0 k l = _
    rw [hχ0, E.amplitude_zero, hU]
    simp only [one_smul, Matrix.one_apply, one_mul]
    ring
  rw [hzero] at h
  apply h.congr'
  exact Eventually.of_forall fun t => by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [heatNormalOneCutoffParametrix, heatNormalOneParametrix,
        fourHeatOnePolynomial, fourHeatPolynomial, u]
      ring


variable [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.one_initial (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (v : smoothCovariantFields M 1) (l : Fin 4) :
    Tendsto (fun t => inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear v))
      (𝓝[Ioi 0] 0) (𝓝 ((normalizedChartFactor g).toReal * heatNormalOneValue c D.point v 0 l)) := by
  let f := fun k x => frameExponentialJacobian g o e x * heatNormalOneValue c D.point v x k
  have hf (k : Fin 4) : ContinuousOn (f k) P.chart.source := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    exact (frameExponentialJacobian_continuous g o e).continuousAt.mul
      (heatNormalOneFormValue_regular 2 c D.point v x
        (P.point_regular.contDiffAt (P.chart.open_source.mem_nhds hx))
        (D.in_chart x (P.inside_radius hx)) k).continuousAt
  have hχf (k : Fin 4) : Continuous (fun x => P.cutoff x * f k x) :=
    heat_continuous_mul_of_tsupport_subset P.cutoff_regular.continuous P.chart.open_source
      (hf k) P.cutoff_support
  have h := (tendsto_finsetSum Finset.univ fun k _ =>
    heatNormalOneCutoffParametrix_initial_local E P.cutoff (f k) (hχf k)
      P.cutoff_compact P.cutoff_zero k l).const_mul (normalizedChartFactor g).toReal
  have hz : (∑ k : Fin 4, (if k = l then 1 else 0) * f k 0) = heatNormalOneValue c D.point v 0 l := by
    simp [f, frameExponentialJacobian_zero]
  rw [hz] at h
  apply h.congr'
  exact Eventually.of_forall fun t => (heatNormalOneAmplitudeL2_pairing_sum
    P.chart P.exponential P.in_chart P.point_regular P.inside_radius
    (heatNormalOneCutoffColumn E P.cutoff t l)
    ((heatNormalOneCutoffColumn_regular E P.cutoff P.cutoff_regular t l).of_le (by norm_num))
    (P.cutoff_compact.of_isClosed_subset (isClosed_tsupport _)
      (heatNormalOneCutoffColumn_support E P.cutoff t l))
    ((heatNormalOneCutoffColumn_support E P.cutoff t l).trans P.cutoff_support) v).symm

theorem HeatNormalParametrixData.one_normalized_initial (P : HeatNormalParametrixData D)
    (E : HeatNormalOneExtension D) (he : e.base ∈ (chartAt FourSpace c).source)
    (v : smoothCovariantFields M 1) (l : Fin 4) :
    Tendsto (fun t => inner ℝ (P.oneNormalizedColumn E t l) (smoothOneFormL2Linear v))
      (𝓝[Ioi 0] 0) (𝓝 (covariantFieldFramed g v.val e ![l])) := by
  have hv : heatNormalOneValue c D.point v 0 l = covariantFieldFramed g v.val e ![l] := by
    change frameTensor (D.point 0).2 (covariantFieldCoordinates v.val c (D.point 0).1) ![l] = _
    rw [D.initial]
    exact (congrFun (heat_covariantField_chart g v.val c e he) ![l]).symm
  have h := (P.one_initial E v l).const_mul ((normalizedChartFactor g).toReal)⁻¹
  rw [hv, ← mul_assoc, inv_mul_cancel₀ (normalizedChartFactor_toReal_pos g).ne', one_mul] at h
  simpa only [HeatNormalParametrixData.oneNormalizedColumn, real_inner_smul_left] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Each actual smooth one-form eigenmode obeys the forced heat equation
for the genuinely constructed normal parametrix. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped Manifold ContDiff _root_.Topology Matrix.Norms.Elementwise
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.one_eigen_evolution
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (t : ℝ) (ht : 0 < t) (l : Fin 4) (i : OneFormEigenIndex hRic d) :
    HasDerivAt (fun s => inner ℝ (P.oneColumn E s l) (oneFormEigenvector hRic d i))
      (inner ℝ (P.oneResidual E t l) (oneFormEigenvector hRic d i) -
        oneFormHeatRate hRic d i * inner ℝ (P.oneColumn E t l) (oneFormEigenvector hRic d i)) t := by
  obtain ⟨v, hv, hLv⟩ := oneFormEigenvector_smooth hRic d i
  have hL : smoothOneFormL2Linear (o := o) (smoothOneFormHodgeLaplacian (o := o) v) =
      oneFormHeatRate hRic d i • oneFormEigenvector hRic d i := by
    rw [hLv, map_smul, ← hv]
  have h := P.oneWeakEvolution E hpair t ht l v
  rw [hL, real_inner_smul_right, ← hv] at h
  exact h

theorem HeatNormalParametrixData.one_normalized_eigen_evolution
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (t : ℝ) (ht : 0 < t) (l : Fin 4) (i : OneFormEigenIndex hRic d) :
    HasDerivAt (fun s => inner ℝ (P.oneNormalizedColumn E s l) (oneFormEigenvector hRic d i))
      (inner ℝ (P.oneNormalizedResidual E t l) (oneFormEigenvector hRic d i) -
        oneFormHeatRate hRic d i * inner ℝ (P.oneNormalizedColumn E t l) (oneFormEigenvector hRic d i)) t := by
  have h := (P.one_eigen_evolution E hpair hRic d t ht l i).const_mul ((normalizedChartFactor g).toReal)⁻¹
  simpa only [HeatNormalParametrixData.oneNormalizedColumn, HeatNormalParametrixData.oneNormalizedResidual,
    real_inner_smul_left, mul_sub, mul_left_comm] using h


end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The actual one-form parametrix satisfies Duhamel's formula in every
smooth eigenmode, with its proved normalized delta initial value. -/

namespace PositiveEinsteinFour.Geometry
open EinsteinFour Set Filter MeasureTheory
open scoped ContDiff Manifold _root_.Topology
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] [Nonempty M] [SecondCountableTopology M]
  {g : SmoothMetric M} {o : FrameOrientation g} {c : M} {e : FrameBundle g}
  {D : HeatNormalFrameData g o c e}

theorem HeatNormalParametrixData.one_normalized_eigen_integral
    (P : HeatNormalParametrixData D) (E : HeatNormalOneExtension D)
    (hpair : ∀ t l (v : smoothCovariantFields M 1),
      inner ℝ (P.oneColumn E t l) (smoothOneFormL2Linear (smoothOneFormHodgeLaplacian (o := o) v)) =
        inner ℝ (P.oneOperatorColumn E t l) (smoothOneFormL2Linear v))
    (hRic : RicciThree g) (d : ParallelMetricData g (canonicalFrameMeasure g o))
    (he : e.base ∈ (chartAt FourSpace c).source)
    (B : ℝ) (hB : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ l, ‖P.oneResidual E t l‖ ≤ B * t)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (l : Fin 4) (i : OneFormEigenIndex hRic d) :
    inner ℝ (P.oneNormalizedColumn E t l) (oneFormEigenvector hRic d i) =
      Real.exp (-oneFormHeatRate hRic d i * t) *
        covariantFieldFramed g (oneFormEigenSection hRic d i).val e ![l] +
      ∫ s in (0 : ℝ)..t, Real.exp (-oneFormHeatRate hRic d i * (t - s)) *
        inner ℝ (P.oneNormalizedResidualZero E s l) (oneFormEigenvector hRic d i) := by
  apply heat_forced_scalar_formula _ _ _ _ t ht.1
  · exact ((P.oneNormalizedResidualZero_continuous E B hB l).mono
      (Icc_subset_Icc le_rfl ht.2)).inner continuousOn_const
  · have h := P.one_normalized_initial E he (oneFormEigenSection hRic d i) l
    simpa only [oneFormEigenSection_L2] using h
  · intro s hs
    rw [P.oneNormalizedResidualZero_eq E s hs l]
    exact P.one_normalized_eigen_evolution E hpair hRic d s hs l i

end
end PositiveEinsteinFour.Geometry
end


end OAI
end


