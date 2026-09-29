-- Prove2me | solution 1 for AutomorphicForm.GL2Real.exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/cba43c3b-54a0-54b3-b8b0-3a4f81d94532

import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight

set_option autoImplicit false

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.AutomorphicForm AutomorphicForm.GL2Real P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.AutomorphicForm.GL2Real"

noncomputable section

section WeightedImage

open MeasureTheory Set UpperHalfPlane
open scoped NNReal ENNReal

namespace FLT
namespace BandStripFubini

private def hypDensity (w : ℂ) : ℝ≥0∞ := (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)

@[scoped simp] private lemma hypDensity_def (w : ℂ) :
    hypDensity w = (((1 / ‖w.im‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) := rfl

private lemma measurable_hypDensity : Measurable hypDensity := by
  unfold hypDensity
  fun_prop

private lemma hypDensity_eq_ofReal (w : ℂ) : hypDensity w = ENNReal.ofReal (w.im⁻¹ ^ 2) := by
  rw [hypDensity_def, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  push_cast
  rw [Real.norm_eq_abs, one_div, inv_pow, sq_abs, ← inv_pow]

private lemma hypDensity_coe (z : ℍ) :
    (((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞) = hypDensity (z : ℂ) := by
  rw [hypDensity_def]
  congr 1
  ext
  push_cast
  rw [UpperHalfPlane.coe_im, Real.norm_eq_abs, abs_of_pos z.im_pos]

private theorem setLIntegral_eq_lintegral_image (f : ℍ → ℝ≥0∞) (hf : Measurable f)
    {S : Set ℍ} (hS : MeasurableSet S) :
    ∫⁻ z in S, f z = ∫⁻ w in (↑) '' S, (↑ₕf) w * hypDensity w := by
  have hmp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  have hdens_meas : Measurable fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    have h : Measurable fun z : ℍ => hypDensity (z : ℂ) :=
      measurable_hypDensity.comp measurable_coe
    exact (funext fun z => hypDensity_coe z) ▸ h
  rw [show (volume : Measure ℍ) = (volume.comap UpperHalfPlane.coe).withDensity
      (fun z => (((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞)) from rfl,
    setLIntegral_withDensity_eq_setLIntegral_mul _ hdens_meas hf hS]
  have hcongr : ∀ z : ℍ,
      ((fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞)) * f) z =
        (fun w : ℂ => (↑ₕf) w * hypDensity w) (z : ℂ) := by
    intro z
    simp only [Pi.mul_apply, Function.comp_apply, ofComplex_apply, hypDensity_coe z]
    ring
  rw [lintegral_congr hcongr]
  rw [hmp.setLIntegral_comp_emb measurableEmbedding_coe
    (fun w => (↑ₕf) w * hypDensity w) S]
  rw [Measure.restrict_restrict' measurableEmbedding_coe.measurableSet_range,
    Set.inter_eq_self_of_subset_left (Set.image_subset_range _ _)]

end FLT.BandStripFubini
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT"

end WeightedImage
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

section PolarRadius

open MeasureTheory Set UpperHalfPlane Real
open scoped Real NNReal ENNReal

namespace FLT
namespace GeodesicPolar

private lemma norm_polarCoord_symm_of_pos {p : ℝ × ℝ} (hp : 0 < p.1) :
    ‖Complex.polarCoord.symm p‖ = p.1 := by
  rw [Complex.norm_polarCoord_symm, abs_of_pos hp]

end FLT.GeodesicPolar
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

end PolarRadius
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

section DiscEngine

open UpperHalfPlane Complex MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace KwTccA13EllipticPointPairEvaluation

private theorem kw_tcc_a13_axiomAnchor : True := by
  have _p : (True = True) := propext Iff.rfl
  have _c := Classical.choice ⟨(0 : ℕ)⟩
  have _q : Quot.mk (α := ℕ) (· = ·) 0 = Quot.mk (· = ·) 0 := Quot.sound rfl
  trivial

private def kw_tcc_a13_cayley (w : ℂ) : ℂ :=
  have _ := kw_tcc_a13_axiomAnchor
  Complex.I * (1 + w) / (1 - w)

private theorem kw_tcc_a13_cayley_def (w : ℂ) :
    kw_tcc_a13_cayley w = Complex.I * (1 + w) / (1 - w) := rfl

private theorem kw_tcc_a13_one_sub_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : (1 : ℂ) - w ≠ 0 := by
  have _ := kw_tcc_a13_axiomAnchor
  intro h
  have : w = 1 := by linear_combination -h
  rw [this] at hw
  simp at hw

private theorem kw_tcc_a13_normSq_one_sub_pos {w : ℂ} (hw : ‖w‖ < 1) :
    0 < Complex.normSq (1 - w) :=
  Complex.normSq_pos.mpr (kw_tcc_a13_one_sub_ne_zero hw)

private theorem kw_tcc_a13_normSq_lt_one {w : ℂ} (hw : ‖w‖ < 1) : Complex.normSq w < 1 := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [Complex.normSq_eq_norm_sq]
  nlinarith [norm_nonneg w]

private theorem kw_tcc_a13_cayley_im (w : ℂ) :
    (kw_tcc_a13_cayley w).im = (1 - Complex.normSq w) / Complex.normSq (1 - w) := by
  have _ := kw_tcc_a13_axiomAnchor
  simp only [kw_tcc_a13_cayley, Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  ring

private theorem kw_tcc_a13_cayley_im_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (kw_tcc_a13_cayley w).im := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [kw_tcc_a13_cayley_im]
  exact div_pos (by linarith [kw_tcc_a13_normSq_lt_one hw])
    (kw_tcc_a13_normSq_one_sub_pos hw)

private theorem kw_tcc_a13_cayley_sub_I {w : ℂ} (hw : ‖w‖ < 1) :
    kw_tcc_a13_cayley w - Complex.I = 2 * Complex.I * w / (1 - w) := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [kw_tcc_a13_cayley_def, div_sub' (hc := kw_tcc_a13_one_sub_ne_zero hw)]
  congr 1
  ring

private theorem kw_tcc_a13_normSq_cayley_sub_I {w : ℂ} (hw : ‖w‖ < 1) :
    Complex.normSq (kw_tcc_a13_cayley w - Complex.I)
      = 4 * Complex.normSq w / Complex.normSq (1 - w) := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [kw_tcc_a13_cayley_sub_I hw, map_div₀, map_mul, map_mul, Complex.normSq_I, mul_one]
  norm_num

private theorem kw_tcc_a13_cosh_dist_cayley_I {w : ℂ} (hw : ‖w‖ < 1) :
    Real.cosh (dist (UpperHalfPlane.mk (kw_tcc_a13_cayley w) (kw_tcc_a13_cayley_im_pos hw))
        UpperHalfPlane.I)
      = (1 + Complex.normSq w) / (1 - Complex.normSq w) := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [UpperHalfPlane.cosh_dist, dist_eq_norm, ← Complex.normSq_eq_norm_sq,
    UpperHalfPlane.coe_mk, UpperHalfPlane.coe_I, UpperHalfPlane.mk_im, UpperHalfPlane.I_im,
    kw_tcc_a13_normSq_cayley_sub_I hw, kw_tcc_a13_cayley_im]
  have h1 := kw_tcc_a13_normSq_one_sub_pos hw
  have h2 := kw_tcc_a13_normSq_lt_one hw
  have h3 : 1 - Complex.normSq w ≠ 0 := by linarith
  field_simp
  ring

private theorem kw_tcc_a13_hypDensity_cayley (w : ℂ) :
    FLT.BandStripFubini.hypDensity (kw_tcc_a13_cayley w)
      = ENNReal.ofReal ((Complex.normSq (1 - w)) ^ 2 / (1 - Complex.normSq w) ^ 2) := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [FLT.BandStripFubini.hypDensity_eq_ofReal, kw_tcc_a13_cayley_im, inv_div, div_pow]

private theorem kw_tcc_a13_cayley_hasDerivAt {w : ℂ} (hw : (1 : ℂ) - w ≠ 0) :
    HasDerivAt kw_tcc_a13_cayley (2 * Complex.I / (1 - w) ^ 2) w := by
  have _ := kw_tcc_a13_axiomAnchor
  have h1 : HasDerivAt (fun z : ℂ => Complex.I * (1 + z)) Complex.I w := by
    simpa using (((hasDerivAt_id w).const_add 1).const_mul Complex.I)
  have h2 : HasDerivAt (fun z : ℂ => (1 : ℂ) - z) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 1
  have h3 := h1.div h2 hw
  have hfun : kw_tcc_a13_cayley = fun z : ℂ => Complex.I * (1 + z) / (1 - z) := by
    funext z
    rw [kw_tcc_a13_cayley_def]
  rw [hfun]
  convert h3 using 1
  · rfl
  · rfl
  · rfl
  field_simp
  ring

private theorem kw_tcc_a13_cayley_abs_det_deriv (w : ℂ) :
    |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ).det|
      = 4 / (Complex.normSq (1 - w)) ^ 2 := by
  have _ := kw_tcc_a13_axiomAnchor
  have hdet : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ).det
      = Complex.normSq (2 * Complex.I / (1 - w) ^ 2) := by
    simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars, Algebra.norm_complex_eq]
  rw [hdet, map_div₀, map_pow, map_mul, Complex.normSq_I, mul_one, abs_div,
    abs_of_nonneg (Complex.normSq_nonneg _), abs_of_nonneg (by positivity)]
  norm_num

private theorem kw_tcc_a13_cayley_injOn :
    Set.InjOn kw_tcc_a13_cayley (Metric.ball (0 : ℂ) 1) := by
  have _ := kw_tcc_a13_axiomAnchor
  intro w₁ h₁ w₂ h₂ heq
  simp only [Metric.mem_ball, dist_zero_right] at h₁ h₂
  have hn₁ := kw_tcc_a13_one_sub_ne_zero h₁
  have hn₂ := kw_tcc_a13_one_sub_ne_zero h₂
  rw [kw_tcc_a13_cayley_def, kw_tcc_a13_cayley_def, div_eq_div_iff hn₁ hn₂] at heq
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2 : Complex.I * (2 * (w₁ - w₂)) = 0 := by linear_combination heq
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h hI
  · rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · exact sub_eq_zero.mp h

private theorem kw_tcc_a13_cayley_image_ball :
    kw_tcc_a13_cayley '' Metric.ball (0 : ℂ) 1 = {z : ℂ | 0 < z.im} := by
  have _ := kw_tcc_a13_axiomAnchor
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [Metric.mem_ball, dist_zero_right] at hw
    exact kw_tcc_a13_cayley_im_pos hw
  · intro hz
    simp only [Set.mem_setOf_eq] at hz
    have hzi : z + Complex.I ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    refine ⟨(z - Complex.I) / (z + Complex.I), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, norm_div, div_lt_one (norm_pos_iff.mpr hzi)]
      have h1 : ‖z - Complex.I‖ ^ 2 < ‖z + Complex.I‖ ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
        simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im,
          Complex.sub_im, Complex.I_re, Complex.I_im, add_zero, sub_zero]
        nlinarith
      nlinarith [norm_nonneg (z - Complex.I), norm_nonneg (z + Complex.I)]
    · rw [kw_tcc_a13_cayley_def]
      have hone : (1 : ℂ) - (z - Complex.I) / (z + Complex.I)
          = 2 * Complex.I / (z + Complex.I) := by
        field_simp
        ring
      have htwo : (1 : ℂ) + (z - Complex.I) / (z + Complex.I) = 2 * z / (z + Complex.I) := by
        field_simp
        ring
      rw [hone, htwo]
      field_simp

private theorem kw_tcc_a13_step1 (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z : ℍ, Ψ (Real.cosh (dist z UpperHalfPlane.I))
      = ∫⁻ w in {w : ℂ | 0 < w.im},
          Ψ (Real.cosh (dist (UpperHalfPlane.ofComplex w) UpperHalfPlane.I))
            * FLT.BandStripFubini.hypDensity w := by
  have _ := kw_tcc_a13_axiomAnchor
  have hf : Measurable fun z : ℍ => Ψ (Real.cosh (dist z UpperHalfPlane.I)) :=
    hΨ.comp ((Real.continuous_cosh.comp (continuous_id.dist continuous_const)).measurable)
  have himg : (UpperHalfPlane.coe '' (Set.univ : Set ℍ)) = {w : ℂ | 0 < w.im} := by
    ext w
    constructor
    · rintro ⟨z, -, rfl⟩
      exact z.im_pos
    · intro hw
      exact ⟨⟨w, hw⟩, Set.mem_univ _, rfl⟩
  rw [← setLIntegral_univ, FLT.BandStripFubini.setLIntegral_eq_lintegral_image _ hf
    MeasurableSet.univ, himg]
  rfl

private theorem kw_tcc_a13_step2 (G : ℂ → ℝ≥0∞) :
    ∫⁻ w in {w : ℂ | 0 < w.im}, G w
      = ∫⁻ w in Metric.ball (0 : ℂ) 1,
          ENNReal.ofReal (4 / (Complex.normSq (1 - w)) ^ 2) * G (kw_tcc_a13_cayley w) := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [← kw_tcc_a13_cayley_image_ball,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball
      (f' := fun w => ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        (2 * Complex.I / (1 - w) ^ 2)).restrictScalars ℝ))
      (fun w hw => ((kw_tcc_a13_cayley_hasDerivAt (kw_tcc_a13_one_sub_ne_zero (by
        simpa using hw))).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
      kw_tcc_a13_cayley_injOn G]
  refine setLIntegral_congr_fun measurableSet_ball (fun w _ => ?_)
  rw [kw_tcc_a13_cayley_abs_det_deriv]

private theorem kw_tcc_a13_step3 (Ψ : ℝ → ℝ≥0∞) {w : ℂ} (hw : ‖w‖ < 1) :
    ENNReal.ofReal (4 / (Complex.normSq (1 - w)) ^ 2)
        * (Ψ (Real.cosh (dist (UpperHalfPlane.ofComplex (kw_tcc_a13_cayley w))
            UpperHalfPlane.I))
          * FLT.BandStripFubini.hypDensity (kw_tcc_a13_cayley w))
      = Ψ ((1 + Complex.normSq w) / (1 - Complex.normSq w))
          * ENNReal.ofReal (4 / (1 - Complex.normSq w) ^ 2) := by
  have _ := kw_tcc_a13_axiomAnchor
  have himpos := kw_tcc_a13_cayley_im_pos hw
  have hof : UpperHalfPlane.ofComplex (kw_tcc_a13_cayley w)
      = UpperHalfPlane.mk (kw_tcc_a13_cayley w) himpos :=
    UpperHalfPlane.ofComplex_apply_of_im_pos himpos
  rw [hof, kw_tcc_a13_cosh_dist_cayley_I hw, kw_tcc_a13_hypDensity_cayley w]
  have hN := kw_tcc_a13_normSq_one_sub_pos hw
  have h4 : (0 : ℝ) ≤ 4 / (Complex.normSq (1 - w)) ^ 2 := by positivity
  have hprod : (4 / (Complex.normSq (1 - w)) ^ 2)
      * ((Complex.normSq (1 - w)) ^ 2 / (1 - Complex.normSq w) ^ 2)
      = 4 / (1 - Complex.normSq w) ^ 2 := by
    have h1 : (Complex.normSq (1 - w)) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [mul_comm (Ψ _) _, ← mul_assoc, ← ENNReal.ofReal_mul h4, hprod, mul_comm]

private theorem kw_tcc_a13_polarCoord_symm_mem_ball_iff {p : ℝ × ℝ} (hp : p ∈ polarCoord.target) :
    Complex.polarCoord.symm p ∈ Metric.ball (0 : ℂ) 1
      ↔ p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi := by
  have _ := kw_tcc_a13_axiomAnchor
  obtain ⟨hr, hθ⟩ := hp
  simp only [Set.mem_Ioi] at hr
  simp only [Set.mem_Ioo] at hθ
  rw [Metric.mem_ball, dist_zero_right, FLT.GeodesicPolar.norm_polarCoord_symm_of_pos hr]
  simp only [Set.mem_prod, Set.mem_Ioo]
  exact ⟨fun h => ⟨⟨hr, h⟩, hθ⟩, fun h => h.1.2⟩

private theorem kw_tcc_a13_normSq_polarCoord_symm {p : ℝ × ℝ} (hp : 0 < p.1) :
    Complex.normSq (Complex.polarCoord.symm p) = p.1 ^ 2 := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [Complex.normSq_eq_norm_sq, FLT.GeodesicPolar.norm_polarCoord_symm_of_pos hp]

private theorem kw_tcc_a13_box_subset_target :
    Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi ⊆ polarCoord.target := by
  have _ := kw_tcc_a13_axiomAnchor
  rintro ⟨r, θ⟩ ⟨hr, hθ⟩
  exact ⟨hr.1, hθ⟩

private theorem kw_tcc_a13_step45 (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ w in Metric.ball (0 : ℂ) 1, H (Complex.normSq w)
      = ENNReal.ofReal (2 * Real.pi)
          * ∫⁻ r in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal r * H (r ^ 2) := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [← lintegral_indicator measurableSet_ball, ← Complex.lintegral_comp_polarCoord_symm,
    ← lintegral_indicator polarCoord.open_target.measurableSet]
  have hpt : ∀ p : ℝ × ℝ,
      polarCoord.target.indicator
        (fun p => ENNReal.ofReal p.1 •
          (Metric.ball (0 : ℂ) 1).indicator (fun w => H (Complex.normSq w))
            (Complex.polarCoord.symm p)) p
        = (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
            (fun p => (ENNReal.ofReal p.1 * H (p.1 ^ 2)) * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2) p := by
    intro p
    by_cases hp : p ∈ polarCoord.target
    · rw [Set.indicator_of_mem hp]
      by_cases hbox : p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi
      · rw [Set.indicator_of_mem hbox,
          Set.indicator_of_mem ((kw_tcc_a13_polarCoord_symm_mem_ball_iff hp).mpr hbox),
          smul_eq_mul, kw_tcc_a13_normSq_polarCoord_symm hp.1]
        simp
      · rw [Set.indicator_of_notMem hbox,
          Set.indicator_of_notMem
            (fun h => hbox ((kw_tcc_a13_polarCoord_symm_mem_ball_iff hp).mp h)),
          smul_zero]
    · rw [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem (fun h => hp (kw_tcc_a13_box_subset_target h))]
  rw [lintegral_congr hpt, lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal r * H (r ^ 2))
      (g := fun _ : ℝ => (1 : ℝ≥0∞))
      ((ENNReal.measurable_ofReal.comp measurable_id).mul
        (hH.comp (measurable_id.pow_const 2))).aemeasurable
      measurable_const.aemeasurable]
  rw [setLIntegral_const, one_mul, Real.volume_Ioo, mul_comm]
  congr 1
  ring_nf

private def kw_tcc_a13_radMap (r : ℝ) : ℝ :=
  have _ := kw_tcc_a13_axiomAnchor
  (1 + r ^ 2) / (1 - r ^ 2)

private theorem kw_tcc_a13_radMap_def (r : ℝ) : kw_tcc_a13_radMap r = (1 + r ^ 2) / (1 - r ^ 2) :=
  rfl

private theorem kw_tcc_a13_radMap_hasDerivAt {r : ℝ} (hr : 1 - r ^ 2 ≠ 0) :
    HasDerivAt kw_tcc_a13_radMap (4 * r / (1 - r ^ 2) ^ 2) r := by
  have _ := kw_tcc_a13_axiomAnchor
  have h1 : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).const_add 1
  have h2 : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-(2 * r)) r := by
    simpa using (hasDerivAt_pow 2 r).const_sub 1
  have h3 := h1.div h2 hr
  have hfun : kw_tcc_a13_radMap = fun x : ℝ => (1 + x ^ 2) / (1 - x ^ 2) := by
    funext x
    rw [kw_tcc_a13_radMap_def]
  rw [hfun]
  convert h3 using 1
  · rfl
  · rfl
  · rfl
  field_simp
  ring

private theorem kw_tcc_a13_radMap_injOn :
    Set.InjOn kw_tcc_a13_radMap (Set.Ioo (0 : ℝ) 1) := by
  have _ := kw_tcc_a13_axiomAnchor
  intro a ha b hb heq
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  have ha2 : 1 - a ^ 2 ≠ 0 := by nlinarith
  have hb2 : 1 - b ^ 2 ≠ 0 := by nlinarith
  rw [kw_tcc_a13_radMap_def, kw_tcc_a13_radMap_def, div_eq_div_iff ha2 hb2] at heq
  have h : a ^ 2 = b ^ 2 := by nlinarith
  nlinarith

private theorem kw_tcc_a13_radMap_image :
    kw_tcc_a13_radMap '' Set.Ioo (0 : ℝ) 1 = Set.Ioi (1 : ℝ) := by
  have _ := kw_tcc_a13_axiomAnchor
  ext v
  constructor
  · rintro ⟨r, ⟨hr0, hr1⟩, rfl⟩
    rw [Set.mem_Ioi, kw_tcc_a13_radMap_def]
    have h1 : 0 < 1 - r ^ 2 := by nlinarith
    rw [lt_div_iff₀ h1]
    nlinarith
  · intro hv
    rw [Set.mem_Ioi] at hv
    refine ⟨Real.sqrt ((v - 1) / (v + 1)), ⟨?_, ?_⟩, ?_⟩
    · exact Real.sqrt_pos.mpr (div_pos (by linarith) (by linarith))
    · have h1 : Real.sqrt ((v - 1) / (v + 1)) < Real.sqrt 1 :=
        Real.sqrt_lt_sqrt (le_of_lt (div_pos (by linarith) (by linarith)))
          (by rw [div_lt_one (by linarith)]; linarith)
      rwa [Real.sqrt_one] at h1
    · rw [kw_tcc_a13_radMap_def,
        Real.sq_sqrt (le_of_lt (div_pos (by linarith) (by linarith)))]
      have hv1 : (v + 1) ≠ 0 := by linarith
      field_simp
      ring

private theorem kw_tcc_a13_step6 (Ψ : ℝ → ℝ≥0∞) :
    ∫⁻ r in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal r * (Ψ ((1 + r ^ 2) / (1 - r ^ 2))
          * ENNReal.ofReal (4 / (1 - r ^ 2) ^ 2))
      = ∫⁻ v in Set.Ioi (1 : ℝ), Ψ v := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [← kw_tcc_a13_radMap_image,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (f' := fun r : ℝ => 4 * r / (1 - r ^ 2) ^ 2)
      (fun r hr => (kw_tcc_a13_radMap_hasDerivAt (by
        obtain ⟨h0, h1⟩ := hr
        nlinarith)).hasDerivWithinAt)
      kw_tcc_a13_radMap_injOn Ψ]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
  obtain ⟨hr0, hr1⟩ := hr
  have hpos : 0 ≤ 4 * r / (1 - r ^ 2) ^ 2 := by
    have : 0 < 1 - r ^ 2 := by nlinarith
    positivity
  rw [abs_of_nonneg hpos, kw_tcc_a13_radMap_def, mul_comm (Ψ _) _, ← mul_assoc,
    ← ENNReal.ofReal_mul (le_of_lt hr0)]
  congr 2
  field_simp

private theorem kw_tcc_a13_disc_polarAboutI (Ψ : ℝ → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ z : ℍ, Ψ (Real.cosh (dist z UpperHalfPlane.I))
      = ENNReal.ofReal (2 * Real.pi) * ∫⁻ v in Set.Ioi (1 : ℝ), Ψ v := by
  have _ := kw_tcc_a13_axiomAnchor
  rw [kw_tcc_a13_step1 Ψ hΨ, kw_tcc_a13_step2]
  have hcongr : ∀ w ∈ Metric.ball (0 : ℂ) 1,
      ENNReal.ofReal (4 / (Complex.normSq (1 - w)) ^ 2)
          * (Ψ (Real.cosh (dist (UpperHalfPlane.ofComplex (kw_tcc_a13_cayley w))
              UpperHalfPlane.I))
            * FLT.BandStripFubini.hypDensity (kw_tcc_a13_cayley w))
        = (fun t : ℝ =>
            Ψ ((1 + t) / (1 - t)) * ENNReal.ofReal (4 / (1 - t) ^ 2)) (Complex.normSq w) := by
    intro w hw
    simp only [Metric.mem_ball, dist_zero_right] at hw
    exact kw_tcc_a13_step3 Ψ hw
  rw [setLIntegral_congr_fun measurableSet_ball hcongr]
  have hH : Measurable (fun t : ℝ =>
      Ψ ((1 + t) / (1 - t)) * ENNReal.ofReal (4 / (1 - t) ^ 2)) := by
    refine (hΨ.comp ?_).mul (ENNReal.measurable_ofReal.comp ?_)
    · exact (measurable_const.add measurable_id).div (measurable_const.sub measurable_id)
    · exact measurable_const.div ((measurable_const.sub measurable_id).pow_const 2)
  rw [kw_tcc_a13_step45 _ hH, kw_tcc_a13_step6]

end KwTccA13EllipticPointPairEvaluation
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

end DiscEngine
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

section RawForm

open MeasureTheory Set UpperHalfPlane
open scoped NNReal ENNReal

namespace HyperbolicRadialIntegration

private theorem cosh_dist_I_eq (z : ℍ) :
    Real.cosh (dist z UpperHalfPlane.I) = (z.re ^ 2 + z.im ^ 2 + 1) / (2 * z.im) := by
  have hy : z.im ≠ 0 := z.im_pos.ne'
  rw [UpperHalfPlane.cosh_dist, Complex.dist_eq_re_im, Real.sq_sqrt]
  · simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, UpperHalfPlane.coe_I, Complex.I_re,
      Complex.I_im, UpperHalfPlane.I_im, sub_zero, mul_one]
    field_simp
    ring
  · positivity

private theorem measurable_cosh_dist_I :
    Measurable fun z : ℍ => Real.cosh (dist z UpperHalfPlane.I) :=
  (Real.continuous_cosh.comp (continuous_id.dist continuous_const)).measurable

private theorem map_cosh_dist_I_volume :
    Measure.map (fun z : ℍ => Real.cosh (dist z UpperHalfPlane.I)) (volume : Measure ℍ)
      = ENNReal.ofReal (2 * Real.pi) • (volume : Measure ℝ).restrict (Set.Ioi (1 : ℝ)) := by
  ext s hs
  have h := KwTccA13EllipticPointPairEvaluation.kw_tcc_a13_disc_polarAboutI (s.indicator 1)
    (measurable_one.indicator hs)
  rw [Measure.map_apply measurable_cosh_dist_I hs, Measure.smul_apply, smul_eq_mul,
    ← lintegral_indicator_one (μ := (volume : Measure ℍ)) (measurable_cosh_dist_I hs),
    ← lintegral_indicator_one (μ := (volume : Measure ℝ).restrict (Set.Ioi (1 : ℝ))) hs]
  refine Eq.trans ?_ h
  refine lintegral_congr fun z => ?_
  by_cases hz : Real.cosh (dist z UpperHalfPlane.I) ∈ s <;> simp [hz]

private abbrev planarIntegrand (Φ : ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun p => Φ ((p.1 ^ 2 + p.2 ^ 2 + 1) / (2 * p.2)) / ((p.2 : ℂ) ^ 2)

private theorem integrable_planarIntegrand (Φ : ℝ → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    Integrable (planarIntegrand Φ)
      ((volume : Measure (ℝ × ℝ)).restrict (Set.univ ×ˢ Set.Ioi (0 : ℝ))) := by
  obtain ⟨R, hR, hΦR⟩ := hΦc.exists_pos_le_norm
  obtain ⟨M, hM⟩ := hΦ.bounded_above_of_compact_support hΦc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hS : MeasurableSet (Set.univ ×ˢ Set.Ioi (0 : ℝ) : Set (ℝ × ℝ)) :=
    MeasurableSet.univ.prod measurableSet_Ioi
  have hKc : IsCompact (Set.Icc (-R) R ×ˢ Set.Icc (1 / (2 * R)) (2 * R) : Set (ℝ × ℝ)) :=
    isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet (Set.Icc (-R) R ×ˢ Set.Icc (1 / (2 * R)) (2 * R) : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hmaj : Integrable
      ((Set.Icc (-R) R ×ˢ Set.Icc (1 / (2 * R)) (2 * R) : Set (ℝ × ℝ)).indicator
        fun _ : ℝ × ℝ => M * (2 * R) ^ 2)
      ((volume : Measure (ℝ × ℝ)).restrict (Set.univ ×ˢ Set.Ioi (0 : ℝ))) :=
    ((integrableOn_const hKc.measure_lt_top.ne).integrable_indicator hKm).integrableOn
  refine Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ hS
    have h2 : ∀ p ∈ (Set.univ ×ˢ Set.Ioi (0 : ℝ) : Set (ℝ × ℝ)), (2 : ℝ) * p.2 ≠ 0 := by
      intro p hp
      have hy : (0 : ℝ) < p.2 := hp.2
      positivity
    have hin : ContinuousOn (fun p : ℝ × ℝ => (p.1 ^ 2 + p.2 ^ 2 + 1) / (2 * p.2))
        (Set.univ ×ˢ Set.Ioi (0 : ℝ)) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) h2
    have hden : ∀ p ∈ (Set.univ ×ˢ Set.Ioi (0 : ℝ) : Set (ℝ × ℝ)), ((p.2 : ℂ) ^ 2) ≠ 0 := by
      intro p hp
      have hy : (0 : ℝ) < p.2 := hp.2
      exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hy.ne')
    exact ContinuousOn.div (hΦ.comp_continuousOn hin) (by fun_prop) hden
  · filter_upwards [ae_restrict_mem hS] with p hp
    have hy : (0 : ℝ) < p.2 := hp.2
    by_cases hC : R ≤ ‖(p.1 ^ 2 + p.2 ^ 2 + 1) / (2 * p.2)‖
    · have h0 : planarIntegrand Φ p = 0 := by
        show Φ ((p.1 ^ 2 + p.2 ^ 2 + 1) / (2 * p.2)) / ((p.2 : ℂ) ^ 2) = 0
        rw [hΦR _ hC, zero_div]
      rw [h0, norm_zero, Set.indicator_apply]
      split_ifs <;> positivity
    · have hCR : (p.1 ^ 2 + p.2 ^ 2 + 1) / (2 * p.2) < R := by
        rw [Real.norm_eq_abs] at hC
        exact lt_of_le_of_lt (le_abs_self _) (not_le.mp hC)
      have hpoly : p.1 ^ 2 + p.2 ^ 2 + 1 < R * (2 * p.2) := (div_lt_iff₀ (by positivity)).mp hCR
      have hx2 : p.1 ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (R - p.2)]
      have hy2R : 1 ≤ 2 * R * p.2 := by nlinarith [sq_nonneg p.1, sq_nonneg p.2]
      have hpK : p ∈ (Set.Icc (-R) R ×ˢ Set.Icc (1 / (2 * R)) (2 * R) : Set (ℝ × ℝ)) := by
        rw [Set.mem_prod, Set.mem_Icc, Set.mem_Icc]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · nlinarith
        · nlinarith
        · rw [div_le_iff₀ (by positivity)]
          linarith
        · nlinarith [sq_nonneg p.1]
      rw [Set.indicator_apply, if_pos hpK]
      show ‖Φ ((p.1 ^ 2 + p.2 ^ 2 + 1) / (2 * p.2)) / ((p.2 : ℂ) ^ 2)‖ ≤ M * (2 * R) ^ 2
      rw [norm_div, norm_pow, Complex.norm_of_nonneg hy.le, div_le_iff₀ (by positivity)]
      have hb := hM ((p.1 ^ 2 + p.2 ^ 2 + 1) / (2 * p.2))
      have h1 : (1 : ℝ) ≤ (2 * R * p.2) ^ 2 := one_le_pow₀ hy2R
      nlinarith [mul_nonneg hM0 (sub_nonneg.mpr h1)]

private theorem integral_comap_coe_eq (G : ℂ → ℂ) :
    (∫ z : ℍ, G (z : ℂ) ∂((volume : Measure ℂ).comap UpperHalfPlane.coe))
      = ∫ w in Set.range UpperHalfPlane.coe, G w := by
  have hmp : MeasurePreserving UpperHalfPlane.coe ((volume : Measure ℂ).comap UpperHalfPlane.coe)
      ((volume : Measure ℂ).restrict (Set.range UpperHalfPlane.coe)) :=
    ⟨measurable_coe, by rw [measurableEmbedding_coe.map_comap]⟩
  exact hmp.integral_comp measurableEmbedding_coe G

private theorem measurable_density :
    Measurable fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) := by
  rw [← measurable_coe_nnreal_ennreal_iff]
  have h : (fun z : ℍ => (((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) : ℝ≥0∞))
      = fun z : ℍ => FLT.BandStripFubini.hypDensity (z : ℂ) :=
    funext FLT.BandStripFubini.hypDensity_coe
  rw [h]
  exact FLT.BandStripFubini.measurable_hypDensity.comp measurable_coe

private theorem integral_volume_eq_integral_comap (h : ℍ → ℂ) :
    (∫ z : ℍ, h z)
      = ∫ z : ℍ, ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) • h z
          ∂((volume : Measure ℂ).comap UpperHalfPlane.coe) := by
  rw [UpperHalfPlane.volume_def, integral_withDensity_eq_integral_smul measurable_density]

private theorem smul_eq_planarIntegrand (Φ : ℝ → ℂ) (z : ℍ) :
    ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) • Φ (Real.cosh (dist z UpperHalfPlane.I))
      = planarIntegrand Φ (Complex.measurableEquivRealProd (z : ℂ)) := by
  rw [cosh_dist_I_eq, NNReal.smul_def, Complex.real_smul]
  simp only [planarIntegrand, Complex.measurableEquivRealProd_apply, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  push_cast
  ring

private theorem preimage_eq_range :
    Complex.measurableEquivRealProd ⁻¹' (Set.univ ×ˢ Set.Ioi (0 : ℝ)) = Set.range UpperHalfPlane.coe := by
  ext w
  simp [Complex.measurableEquivRealProd_apply, UpperHalfPlane.range_coe]

private theorem integral_integral_eq (Φ : ℝ → ℂ) (hΦ : Continuous Φ) (hΦc : HasCompactSupport Φ) :
    (∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ, Φ ((x ^ 2 + y ^ 2 + 1) / (2 * y)) / ((y : ℂ) ^ 2)) =
      (2 * Real.pi : ℂ) * ∫ c in Set.Ioi (1 : ℝ), Φ c := by
  have hint : Integrable (planarIntegrand Φ)
      ((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) := by
    have h := integrable_planarIntegrand Φ hΦ hΦc
    rwa [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ] at h
  calc (∫ y in Set.Ioi (0 : ℝ), ∫ x : ℝ, Φ ((x ^ 2 + y ^ 2 + 1) / (2 * y)) / ((y : ℂ) ^ 2))
      = ∫ p, planarIntegrand Φ p
          ∂((volume : Measure ℝ).prod ((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ)))) :=
        (integral_prod_symm (planarIntegrand Φ) hint).symm
    _ = ∫ p in (Set.univ ×ˢ Set.Ioi (0 : ℝ) : Set (ℝ × ℝ)), planarIntegrand Φ p := by
        rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    _ = ∫ w in Set.range UpperHalfPlane.coe, planarIntegrand Φ (Complex.measurableEquivRealProd w) := by
        rw [← Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
          Complex.measurableEquivRealProd.measurableEmbedding (planarIntegrand Φ)
          (Set.univ ×ˢ Set.Ioi (0 : ℝ)), preimage_eq_range]
    _ = ∫ z : ℍ, planarIntegrand Φ (Complex.measurableEquivRealProd (z : ℂ))
          ∂((volume : Measure ℂ).comap UpperHalfPlane.coe) :=
        (integral_comap_coe_eq fun w => planarIntegrand Φ (Complex.measurableEquivRealProd w)).symm
    _ = ∫ z : ℍ, ((1 / NNReal.mk z.im z.im_pos.le) ^ 2 : ℝ≥0) • Φ (Real.cosh (dist z UpperHalfPlane.I))
          ∂((volume : Measure ℂ).comap UpperHalfPlane.coe) := by
        congr 1
        funext z
        exact (smul_eq_planarIntegrand Φ z).symm
    _ = ∫ z : ℍ, Φ (Real.cosh (dist z UpperHalfPlane.I)) :=
        (integral_volume_eq_integral_comap fun z => Φ (Real.cosh (dist z UpperHalfPlane.I))).symm
    _ = ∫ v, Φ v ∂(Measure.map (fun z : ℍ => Real.cosh (dist z UpperHalfPlane.I)) (volume : Measure ℍ)) :=
        (integral_map measurable_cosh_dist_I.aemeasurable hΦ.aestronglyMeasurable).symm
    _ = (2 * Real.pi : ℂ) * ∫ c in Set.Ioi (1 : ℝ), Φ c := by
        rw [map_cosh_dist_I_volume, integral_smul_measure, ENNReal.toReal_ofReal, Complex.real_smul]
        · simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
        · positivity

end HyperbolicRadialIntegration
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

end RawForm
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

private noncomputable def circleKernelPoint (v θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I

private noncomputable def hyperbolicAngle (v ψ : ℝ) : ℝ :=
  Real.arsinh (Real.sqrt v * Real.cos ψ)

private noncomputable def hyperbolicKernelPoint (v ψ : ℝ) : ℂ :=
  (Real.cosh (hyperbolicAngle v ψ) : ℂ) + ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I

private noncomputable def chebyshevModeIntegrand (v : ℝ) (n : ℤ) (m : ℕ) (θ : ℝ) : ℝ :=
  (Polynomial.Chebyshev.U ℝ n).eval (Real.cos θ) * (circleKernelPoint v θ ^ m).re * Real.sin θ /
    Real.sqrt (Real.sin θ ^ 2 + v)

private noncomputable def hyperbolicModeIntegrand (κ : ℝ → ℝ) (v : ℝ) (m : ℕ) (ψ : ℝ) : ℝ :=
  κ (hyperbolicAngle v ψ) * (hyperbolicKernelPoint v ψ ^ m).re / Real.cosh (hyperbolicAngle v ψ)

private noncomputable def chebyshevMode (v : ℝ) (n : ℤ) (m : ℕ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi, chebyshevModeIntegrand v n m θ

private noncomputable def hyperbolicMode (κ : ℝ → ℝ) (v : ℝ) (m : ℕ) : ℝ :=
  ∫ ψ in (-(Real.pi / 2))..(Real.pi / 2), hyperbolicModeIntegrand κ v m ψ

private theorem chebyshevMode_eq (v : ℝ) (n m : ℕ) :
    chebyshevMode v n m =
      ∫ θ in (0 : ℝ)..Real.pi,
        (Polynomial.Chebyshev.U ℝ n).eval (Real.cos θ) *
            (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
          Real.sqrt (Real.sin θ ^ 2 + v) := rfl

private theorem hyperbolicMode_sinh_eq (v : ℝ) (n m : ℕ) :
    hyperbolicMode (fun t => Real.sinh (((n : ℝ) + 1) * t)) v m =
      ∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
        Real.sinh (((n : ℝ) + 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
            (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
          Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) := rfl

private theorem hyperbolicMode_cosh_eq (v : ℝ) (n m : ℕ) :
    hyperbolicMode (fun t => Real.cosh (((n : ℝ) + 1) * t)) v m =
      ∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
        Real.cosh (((n : ℝ) + 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
            (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
          Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) := rfl

private theorem two_mul_re_mul_re_pow_succ (w : ℂ) (m : ℕ) :
    2 * w.re * (w ^ (m + 1)).re = (w ^ (m + 2)).re + Complex.normSq w * (w ^ m).re := by
  have hmul : w ^ (m + 1) * ((2 * w.re : ℝ) : ℂ) = w ^ (m + 2) + ((Complex.normSq w : ℝ) : ℂ) * w ^ m := by
    rw [← Complex.add_conj, ← Complex.mul_conj]
    ring
  have h := congrArg Complex.re hmul
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.add_re,
    Complex.re_ofReal_mul] at h
  linear_combination h

private theorem re_circleKernelPoint (v θ : ℝ) : (circleKernelPoint v θ).re = Real.cos θ := by
  simp only [circleKernelPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

private theorem normSq_circleKernelPoint {v : ℝ} (hv : 0 < v) (θ : ℝ) :
    Complex.normSq (circleKernelPoint v θ) = 1 + v := by
  simp only [Complex.normSq_apply, circleKernelPoint, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul,
    sub_zero, add_zero, zero_add]
  rw [Real.mul_self_sqrt (by positivity)]
  linear_combination Real.cos_sq_add_sin_sq θ

private theorem re_hyperbolicKernelPoint (v ψ : ℝ) :
    (hyperbolicKernelPoint v ψ).re = Real.cosh (hyperbolicAngle v ψ) := by
  simp only [hyperbolicKernelPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

private theorem normSq_hyperbolicKernelPoint {v : ℝ} (hv : 0 < v) (ψ : ℝ) :
    Complex.normSq (hyperbolicKernelPoint v ψ) = 1 + v := by
  simp only [Complex.normSq_apply, hyperbolicKernelPoint, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_mul,
    sub_zero, add_zero, zero_add]
  rw [hyperbolicAngle, Real.cosh_arsinh, Real.mul_self_sqrt (by positivity)]
  have hs : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv.le
  linear_combination (Real.cos ψ ^ 2 + Real.sin ψ ^ 2) * hs + v * Real.cos_sq_add_sin_sq ψ

private theorem sinh_kernel_add (a t : ℝ) :
    Real.sinh ((a + 1) * t) + Real.sinh ((a - 1) * t) = 2 * Real.cosh t * Real.sinh (a * t) := by
  rw [add_mul, sub_mul, one_mul, Real.sinh_add, Real.sinh_sub]
  ring

private theorem cosh_kernel_add (a t : ℝ) :
    Real.cosh ((a + 1) * t) + Real.cosh ((a - 1) * t) = 2 * Real.cosh t * Real.cosh (a * t) := by
  rw [add_mul, sub_mul, one_mul, Real.cosh_add, Real.cosh_sub]
  ring

private theorem chebyshevU_eval_add_add_one (n : ℤ) (x : ℝ) :
    (Polynomial.Chebyshev.U ℝ (n + 1)).eval x + (Polynomial.Chebyshev.U ℝ (n - 1)).eval x =
      2 * x * (Polynomial.Chebyshev.U ℝ n).eval x := by
  have h := Polynomial.Chebyshev.U_add_two ℝ (n - 1)
  rw [show n - 1 + 2 = n + 1 by ring, show n - 1 + 1 = n by ring] at h
  have h' := congrArg (Polynomial.eval x) h
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_ofNat] at h'
  linear_combination h'

private theorem continuous_circleKernelPoint (v : ℝ) : Continuous (circleKernelPoint v) := by
  unfold circleKernelPoint
  fun_prop

private theorem continuous_hyperbolicAngle (v : ℝ) : Continuous (hyperbolicAngle v) := by
  show Continuous fun ψ : ℝ => Real.arsinh (Real.sqrt v * Real.cos ψ)
  exact Real.continuous_arsinh.comp (continuous_const.mul Real.continuous_cos)

private theorem continuous_hyperbolicKernelPoint (v : ℝ) : Continuous (hyperbolicKernelPoint v) := by
  show Continuous fun ψ : ℝ =>
    (Real.cosh (hyperbolicAngle v ψ) : ℂ) + ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I
  exact (Complex.continuous_ofReal.comp (Real.continuous_cosh.comp (continuous_hyperbolicAngle v))).add
    ((Complex.continuous_ofReal.comp (continuous_const.mul Real.continuous_sin)).mul continuous_const)

private theorem continuous_chebyshevModeIntegrand {v : ℝ} (hv : 0 < v) (n : ℤ) (m : ℕ) :
    Continuous (chebyshevModeIntegrand v n m) := by
  unfold chebyshevModeIntegrand
  refine Continuous.div ?_ ?_ ?_
  · exact (((Polynomial.Chebyshev.U ℝ n).continuous.comp Real.continuous_cos).mul
      (Complex.continuous_re.comp ((continuous_circleKernelPoint v).pow m))).mul Real.continuous_sin
  · exact Real.continuous_sqrt.comp (by fun_prop)
  · intro θ
    exact (Real.sqrt_pos.mpr (by positivity)).ne'

private theorem continuous_hyperbolicModeIntegrand {κ : ℝ → ℝ} (hκ : Continuous κ) (v : ℝ) (m : ℕ) :
    Continuous (hyperbolicModeIntegrand κ v m) := by
  unfold hyperbolicModeIntegrand
  refine Continuous.div ?_ ?_ ?_
  · exact (hκ.comp (continuous_hyperbolicAngle v)).mul
      (Complex.continuous_re.comp ((continuous_hyperbolicKernelPoint v).pow m))
  · exact Real.continuous_cosh.comp (continuous_hyperbolicAngle v)
  · intro ψ
    exact (Real.cosh_pos _).ne'

private theorem chebyshevMode_add_chebyshevMode {v : ℝ} (hv : 0 < v) (n : ℤ) (m : ℕ) :
    chebyshevMode v (n + 1) (m + 1) + chebyshevMode v (n - 1) (m + 1) =
      chebyshevMode v n (m + 2) + (1 + v) * chebyshevMode v n m := by
  unfold chebyshevMode
  rw [← intervalIntegral.integral_add ((continuous_chebyshevModeIntegrand hv _ _).intervalIntegrable _ _)
      ((continuous_chebyshevModeIntegrand hv _ _).intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((continuous_chebyshevModeIntegrand hv _ _).intervalIntegrable _ _)
      (((continuous_chebyshevModeIntegrand hv _ _).intervalIntegrable _ _).const_mul _)]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [chebyshevModeIntegrand]
  have hU := chebyshevU_eval_add_add_one n (Real.cos θ)
  have halg := two_mul_re_mul_re_pow_succ (circleKernelPoint v θ) m
  rw [re_circleKernelPoint, normSq_circleKernelPoint hv] at halg
  linear_combination
    ((circleKernelPoint v θ ^ (m + 1)).re * Real.sin θ / Real.sqrt (Real.sin θ ^ 2 + v)) * hU +
      ((Polynomial.Chebyshev.U ℝ n).eval (Real.cos θ) * Real.sin θ / Real.sqrt (Real.sin θ ^ 2 + v)) * halg

private theorem hyperbolicMode_add_hyperbolicMode {v : ℝ} (hv : 0 < v) {κ₁ κ₀ κ : ℝ → ℝ}
    (hsum : ∀ t, κ₁ t + κ₀ t = 2 * Real.cosh t * κ t) (h₁ : Continuous κ₁) (h₀ : Continuous κ₀)
    (h : Continuous κ) (m : ℕ) :
    hyperbolicMode κ₁ v (m + 1) + hyperbolicMode κ₀ v (m + 1) =
      hyperbolicMode κ v (m + 2) + (1 + v) * hyperbolicMode κ v m := by
  unfold hyperbolicMode
  rw [← intervalIntegral.integral_add ((continuous_hyperbolicModeIntegrand h₁ v _).intervalIntegrable _ _)
      ((continuous_hyperbolicModeIntegrand h₀ v _).intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((continuous_hyperbolicModeIntegrand h v _).intervalIntegrable _ _)
      (((continuous_hyperbolicModeIntegrand h v _).intervalIntegrable _ _).const_mul _)]
  refine intervalIntegral.integral_congr fun ψ _ => ?_
  simp only [hyperbolicModeIntegrand]
  have hk := hsum (hyperbolicAngle v ψ)
  have halg := two_mul_re_mul_re_pow_succ (hyperbolicKernelPoint v ψ) m
  rw [re_hyperbolicKernelPoint, normSq_hyperbolicKernelPoint hv] at halg
  linear_combination
    ((hyperbolicKernelPoint v ψ ^ (m + 1)).re / Real.cosh (hyperbolicAngle v ψ)) * hk +
      (κ (hyperbolicAngle v ψ) / Real.cosh (hyperbolicAngle v ψ)) * halg

private theorem sinhMode_add_sinhMode {v : ℝ} (hv : 0 < v) (a : ℝ) (m : ℕ) :
    hyperbolicMode (fun t => Real.sinh ((a + 1) * t)) v (m + 1) +
        hyperbolicMode (fun t => Real.sinh ((a - 1) * t)) v (m + 1) =
      hyperbolicMode (fun t => Real.sinh (a * t)) v (m + 2) +
        (1 + v) * hyperbolicMode (fun t => Real.sinh (a * t)) v m :=
  hyperbolicMode_add_hyperbolicMode hv (fun t => sinh_kernel_add a t) (by fun_prop) (by fun_prop) (by fun_prop) m

private theorem coshMode_add_coshMode {v : ℝ} (hv : 0 < v) (a : ℝ) (m : ℕ) :
    hyperbolicMode (fun t => Real.cosh ((a + 1) * t)) v (m + 1) +
        hyperbolicMode (fun t => Real.cosh ((a - 1) * t)) v (m + 1) =
      hyperbolicMode (fun t => Real.cosh (a * t)) v (m + 2) +
        (1 + v) * hyperbolicMode (fun t => Real.cosh (a * t)) v m :=
  hyperbolicMode_add_hyperbolicMode hv (fun t => cosh_kernel_add a t) (by fun_prop) (by fun_prop) (by fun_prop) m

private theorem chebyshevMode_neg_one (v : ℝ) (m : ℕ) : chebyshevMode v (-1) m = 0 := by
  simp [chebyshevMode, chebyshevModeIntegrand, Polynomial.Chebyshev.U_neg_one]

private theorem hyperbolicMode_eq_zero_of_kernel {κ : ℝ → ℝ} (hκ : ∀ t, κ t = 0) (v : ℝ) (m : ℕ) :
    hyperbolicMode κ v m = 0 := by
  simp [hyperbolicMode, hyperbolicModeIntegrand, hκ]

private theorem coshMode_zero (v : ℝ) : hyperbolicMode Real.cosh v 0 = Real.pi := by
  have h : ∀ ψ : ℝ, hyperbolicModeIntegrand Real.cosh v 0 ψ = 1 := fun ψ => by
    simp only [hyperbolicModeIntegrand, pow_zero, Complex.one_re, mul_one]
    exact div_self (Real.cosh_pos _).ne'
  simp only [hyperbolicMode, h, intervalIntegral.integral_const, smul_eq_mul, mul_one]
  ring

private theorem im_circleKernelPoint (v θ : ℝ) : (circleKernelPoint v θ).im = Real.sqrt (Real.sin θ ^ 2 + v) := by
  simp only [circleKernelPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

private theorem im_hyperbolicKernelPoint (v ψ : ℝ) : (hyperbolicKernelPoint v ψ).im = Real.sqrt v * Real.sin ψ := by
  simp only [hyperbolicKernelPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]

private theorem sinh_hyperbolicAngle (v ψ : ℝ) : Real.sinh (hyperbolicAngle v ψ) = Real.sqrt v * Real.cos ψ := by
  simp only [hyperbolicAngle, Real.sinh_arsinh]

private theorem hasDerivAt_sqrt_sin_sq_add {v : ℝ} (hv : 0 < v) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.sqrt (Real.sin θ ^ 2 + v))
      (Real.sin θ * Real.cos θ / Real.sqrt (Real.sin θ ^ 2 + v)) θ := by
  have h0 : Real.sin θ ^ 2 + v ≠ 0 := by positivity
  have hq : Real.sqrt (Real.sin θ ^ 2 + v) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  refine ((((Real.hasDerivAt_sin θ).fun_pow 2).add_const v).sqrt h0).congr_deriv ?_
  try simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  first | (field_simp; ring) | (field_simp; done)

private theorem hasDerivAt_circleKernelPoint {v : ℝ} (hv : 0 < v) (θ : ℝ) :
    HasDerivAt (circleKernelPoint v)
      (Complex.I * circleKernelPoint v θ * ((Real.sin θ / Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ)) θ := by
  have hq : Real.sqrt (Real.sin θ ^ 2 + v) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have h := (Real.hasDerivAt_cos θ).ofReal_comp.add
    ((hasDerivAt_sqrt_sin_sq_add hv θ).ofReal_comp.mul_const Complex.I)
  refine h.congr_deriv ?_
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      re_circleKernelPoint, im_circleKernelPoint, mul_zero, zero_mul, mul_one, one_mul, sub_zero, zero_sub, add_zero,
      zero_add]
    first | (field_simp; done) | (field_simp; ring)
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      re_circleKernelPoint, im_circleKernelPoint, mul_zero, zero_mul, mul_one, one_mul, sub_zero, zero_sub, add_zero,
      zero_add]
    ring

private theorem hasDerivAt_hyperbolicAngle (v ψ : ℝ) :
    HasDerivAt (hyperbolicAngle v) (-(Real.sqrt v * Real.sin ψ) / Real.cosh (hyperbolicAngle v ψ)) ψ := by
  refine ((Real.hasDerivAt_cos ψ).const_mul (Real.sqrt v)).arsinh.congr_deriv ?_
  rw [smul_eq_mul, hyperbolicAngle, Real.cosh_arsinh]
  ring

private theorem hasDerivAt_hyperbolicKernelPoint (v ψ : ℝ) :
    HasDerivAt (hyperbolicKernelPoint v)
      (Complex.I * hyperbolicKernelPoint v ψ *
        ((Real.sinh (hyperbolicAngle v ψ) / Real.cosh (hyperbolicAngle v ψ) : ℝ) : ℂ)) ψ := by
  have hc : Real.cosh (hyperbolicAngle v ψ) ≠ 0 := (Real.cosh_pos _).ne'
  have h := (hasDerivAt_hyperbolicAngle v ψ).cosh.ofReal_comp.add
    (((Real.hasDerivAt_sin ψ).const_mul (Real.sqrt v)).ofReal_comp.mul_const Complex.I)
  refine h.congr_deriv ?_
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      re_hyperbolicKernelPoint, im_hyperbolicKernelPoint, mul_zero, zero_mul, mul_one, one_mul, sub_zero, zero_sub,
      add_zero, zero_add]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      re_hyperbolicKernelPoint, im_hyperbolicKernelPoint, mul_zero, zero_mul, mul_one, one_mul, sub_zero, zero_sub,
      add_zero, zero_add, sinh_hyperbolicAngle]
    first | (field_simp; done) | (field_simp; ring)

private theorem im_deriv_pow_value (z : ℂ) (n : ℕ) (r : ℝ) :
    (((n + 1 : ℕ) : ℂ) * z ^ n * (Complex.I * z * (r : ℂ))).im = ((n : ℝ) + 1) * r * (z ^ (n + 1)).re := by
  have e : ((n + 1 : ℕ) : ℂ) * z ^ n * (Complex.I * z * (r : ℂ)) =
      Complex.I * (((((n : ℝ) + 1) * r : ℝ) : ℂ) * z ^ (n + 1)) := by
    push_cast
    ring
  rw [e, Complex.I_mul_im, Complex.re_ofReal_mul]

private theorem im_deriv_pow_mul_value (z : ℂ) (n : ℕ) (r L K d : ℝ) :
    ((((n + 1 : ℕ) : ℂ) * z ^ n * (Complex.I * z * (r : ℂ))) * (L : ℂ) +
        z ^ (n + 1) * ((K * d : ℝ) : ℂ)).im =
      ((n : ℝ) + 1) * r * L * (z ^ (n + 1)).re + K * d * (z ^ (n + 1)).im := by
  have e : (((n + 1 : ℕ) : ℂ) * z ^ n * (Complex.I * z * (r : ℂ))) * (L : ℂ) +
        z ^ (n + 1) * ((K * d : ℝ) : ℂ) =
      Complex.I * (((((n : ℝ) + 1) * r * L : ℝ) : ℂ) * z ^ (n + 1)) + ((K * d : ℝ) : ℂ) * z ^ (n + 1) := by
    push_cast
    ring
  rw [e, Complex.add_im, Complex.I_mul_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul]

private theorem hasDerivAt_im_pow_circleKernelPoint {v : ℝ} (hv : 0 < v) (k : ℕ) (θ : ℝ) :
    HasDerivAt (fun θ => (circleKernelPoint v θ ^ (k + 1)).im)
      (((k : ℝ) + 1) * chebyshevModeIntegrand v 0 (k + 1) θ) θ := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ ((hasDerivAt_circleKernelPoint hv θ).fun_pow (k + 1))
  refine h.congr_deriv ?_
  rw [Complex.imCLM_apply]
  simp only [Nat.add_sub_cancel]
  rw [im_deriv_pow_value, chebyshevModeIntegrand, Polynomial.Chebyshev.U_zero, Polynomial.eval_one]
  ring

private theorem hasDerivAt_im_pow_hyperbolicKernelPoint (v : ℝ) (k : ℕ) (ψ : ℝ) :
    HasDerivAt (fun ψ => (hyperbolicKernelPoint v ψ ^ (k + 1)).im)
      (((k : ℝ) + 1) * hyperbolicModeIntegrand Real.sinh v (k + 1) ψ) ψ := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt ψ ((hasDerivAt_hyperbolicKernelPoint v ψ).fun_pow (k + 1))
  refine h.congr_deriv ?_
  rw [Complex.imCLM_apply]
  simp only [Nat.add_sub_cancel]
  rw [im_deriv_pow_value, hyperbolicModeIntegrand]
  ring

private theorem chebyshevMode_zero_succ {v : ℝ} (hv : 0 < v) (k : ℕ) :
    chebyshevMode v 0 (k + 1) =
      (circleKernelPoint v Real.pi ^ (k + 1)).im / ((k : ℝ) + 1) -
        (circleKernelPoint v 0 ^ (k + 1)).im / ((k : ℝ) + 1) := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hF : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun θ => (circleKernelPoint v θ ^ (k + 1)).im / ((k : ℝ) + 1))
        (chebyshevModeIntegrand v 0 (k + 1) θ) θ := by
    intro θ _
    have h := (hasDerivAt_im_pow_circleKernelPoint hv k θ).div_const ((k : ℝ) + 1)
    rwa [mul_div_cancel_left₀ _ hk] at h
  unfold chebyshevMode
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((continuous_chebyshevModeIntegrand hv _ _).intervalIntegrable _ _)]

private theorem sinhMode_succ (v : ℝ) (k : ℕ) :
    hyperbolicMode Real.sinh v (k + 1) =
      (hyperbolicKernelPoint v (Real.pi / 2) ^ (k + 1)).im / ((k : ℝ) + 1) -
        (hyperbolicKernelPoint v (-(Real.pi / 2)) ^ (k + 1)).im / ((k : ℝ) + 1) := by
  have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hF : ∀ ψ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt (fun ψ => (hyperbolicKernelPoint v ψ ^ (k + 1)).im / ((k : ℝ) + 1))
        (hyperbolicModeIntegrand Real.sinh v (k + 1) ψ) ψ := by
    intro ψ _
    have h := (hasDerivAt_im_pow_hyperbolicKernelPoint v k ψ).div_const ((k : ℝ) + 1)
    rwa [mul_div_cancel_left₀ _ hk] at h
  unfold hyperbolicMode
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((continuous_hyperbolicModeIntegrand Real.continuous_sinh v _).intervalIntegrable _ _)]

private theorem circleKernelPoint_zero_eq (v : ℝ) : circleKernelPoint v 0 = hyperbolicKernelPoint v (Real.pi / 2) := by
  apply Complex.ext
  · simp [re_circleKernelPoint, re_hyperbolicKernelPoint, hyperbolicAngle, Real.arsinh_zero]
  · simp [im_circleKernelPoint, im_hyperbolicKernelPoint]

private theorem circleKernelPoint_pi_eq (v : ℝ) :
    circleKernelPoint v Real.pi = -hyperbolicKernelPoint v (-(Real.pi / 2)) := by
  apply Complex.ext
  · simp [re_circleKernelPoint, re_hyperbolicKernelPoint, hyperbolicAngle, Real.arsinh_zero]
  · simp [im_circleKernelPoint, im_hyperbolicKernelPoint]

private theorem chebyshevMode_zero_add_sinhMode_of_even {v : ℝ} (hv : 0 < v) {m : ℕ} (hm : Even m) (hm1 : 1 ≤ m) :
    chebyshevMode v 0 m + hyperbolicMode Real.sinh v m = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [chebyshevMode_zero_succ hv k, sinhMode_succ v k, circleKernelPoint_zero_eq, circleKernelPoint_pi_eq, hm.neg_pow]
  ring

private theorem chebyshevMode_zero_zero {v : ℝ} (hv : 0 < v) :
    chebyshevMode v 0 0 = 2 * Real.arctan (Real.sqrt v)⁻¹ := by
  have hF : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun θ : ℝ => -Real.arctan (Real.cos θ / Real.sqrt (Real.sin θ ^ 2 + v)))
        (chebyshevModeIntegrand v 0 0 θ) θ := by
    intro θ _
    have hq : Real.sqrt (Real.sin θ ^ 2 + v) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    have h1 : 1 + (Real.cos θ / Real.sqrt (Real.sin θ ^ 2 + v)) ^ 2 ≠ 0 := by positivity
    refine (((Real.hasDerivAt_cos θ).div (hasDerivAt_sqrt_sin_sq_add hv θ) hq).arctan).neg.congr_deriv ?_
    simp only [chebyshevModeIntegrand, Polynomial.Chebyshev.U_zero, Polynomial.eval_one, pow_zero, Complex.one_re,
      one_mul, Pi.div_apply]
    first | (field_simp; ring) | (field_simp; done)
  unfold chebyshevMode
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((continuous_chebyshevModeIntegrand hv _ _).intervalIntegrable _ _)]
  first | (simp [neg_div, Real.arctan_neg]; ring) | (simp [neg_div, Real.arctan_neg]; done)

private theorem sinhMode_zero (v : ℝ) : hyperbolicMode Real.sinh v 0 = 2 * Real.arctan (Real.sqrt v) := by
  have hF : ∀ ψ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt (fun ψ : ℝ => Real.arctan (Real.sqrt v * Real.sin ψ / Real.cosh (hyperbolicAngle v ψ)))
        (hyperbolicModeIntegrand Real.sinh v 0 ψ) ψ := by
    intro ψ _
    have hc : Real.cosh (hyperbolicAngle v ψ) ≠ 0 := (Real.cosh_pos _).ne'
    have h1 : 1 + (Real.sqrt v * Real.sin ψ / Real.cosh (hyperbolicAngle v ψ)) ^ 2 ≠ 0 := by positivity
    refine ((((Real.hasDerivAt_sin ψ).const_mul (Real.sqrt v)).div (hasDerivAt_hyperbolicAngle v ψ).cosh hc).arctan
      ).congr_deriv ?_
    simp only [hyperbolicModeIntegrand, pow_zero, Complex.one_re, mul_one, Pi.div_apply, sinh_hyperbolicAngle]
    first | (field_simp; ring) | (field_simp; done)
  unfold hyperbolicMode
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    ((continuous_hyperbolicModeIntegrand Real.continuous_sinh v _).intervalIntegrable _ _)]
  first
    | (simp [hyperbolicAngle, Real.arsinh_zero, Real.arctan_neg]; ring)
    | (simp [hyperbolicAngle, Real.arsinh_zero, Real.arctan_neg]; done)

private theorem chebyshevMode_zero_add_sinhMode_zero {v : ℝ} (hv : 0 < v) :
    chebyshevMode v 0 0 + hyperbolicMode Real.sinh v 0 = hyperbolicMode Real.cosh v 0 := by
  rw [chebyshevMode_zero_zero hv, sinhMode_zero v, coshMode_zero, Real.arctan_inv_of_pos (Real.sqrt_pos.mpr hv)]
  ring

private theorem hasDerivAt_edge_antiderivative (v : ℝ) (j : ℕ) (ψ : ℝ) :
    HasDerivAt
      (fun ψ =>
        (hyperbolicKernelPoint v ψ ^ (j + 1) * (Real.sinh (((j : ℝ) + 1) * hyperbolicAngle v ψ) : ℂ)).im)
      (((j : ℝ) + 1) *
        (hyperbolicModeIntegrand (fun t => Real.cosh (((j : ℝ) + 1) * t)) v (j + 2) ψ -
          hyperbolicModeIntegrand (fun t => Real.cosh ((j : ℝ) * t)) v (j + 1) ψ)) ψ := by
  have hP := (hasDerivAt_hyperbolicKernelPoint v ψ).fun_pow (j + 1)
  have hL := (((hasDerivAt_hyperbolicAngle v ψ).const_mul ((j : ℝ) + 1)).sinh).ofReal_comp
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt ψ (hP.mul hL)
  refine h.congr_deriv ?_
  rw [Complex.imCLM_apply]
  simp only [Nat.add_sub_cancel]
  rw [im_deriv_pow_mul_value]
  have hRe2 : (hyperbolicKernelPoint v ψ ^ (j + 2)).re =
      (hyperbolicKernelPoint v ψ ^ (j + 1)).re * Real.cosh (hyperbolicAngle v ψ) -
        (hyperbolicKernelPoint v ψ ^ (j + 1)).im * (Real.sqrt v * Real.sin ψ) := by
    rw [show j + 2 = j + 1 + 1 from rfl, pow_succ, Complex.mul_re, re_hyperbolicKernelPoint, im_hyperbolicKernelPoint]
  have hcj : Real.cosh ((j : ℝ) * hyperbolicAngle v ψ) =
      Real.cosh (((j : ℝ) + 1) * hyperbolicAngle v ψ) * Real.cosh (hyperbolicAngle v ψ) -
        Real.sinh (((j : ℝ) + 1) * hyperbolicAngle v ψ) * Real.sinh (hyperbolicAngle v ψ) := by
    rw [← Real.cosh_sub]
    congr 1
    ring
  simp only [hyperbolicModeIntegrand]
  rw [hRe2, hcj]
  ring

private theorem coshMode_edge (v : ℝ) (j : ℕ) :
    hyperbolicMode (fun t => Real.cosh (((j : ℝ) + 1) * t)) v (j + 2) =
      hyperbolicMode (fun t => Real.cosh ((j : ℝ) * t)) v (j + 1) := by
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  have hc₁ : Continuous (hyperbolicModeIntegrand (fun t => Real.cosh (((j : ℝ) + 1) * t)) v (j + 2)) :=
    continuous_hyperbolicModeIntegrand (by fun_prop) v _
  have hc₀ : Continuous (hyperbolicModeIntegrand (fun t => Real.cosh ((j : ℝ) * t)) v (j + 1)) :=
    continuous_hyperbolicModeIntegrand (by fun_prop) v _
  have hF : ∀ ψ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt
        (fun ψ =>
          (hyperbolicKernelPoint v ψ ^ (j + 1) * (Real.sinh (((j : ℝ) + 1) * hyperbolicAngle v ψ) : ℂ)).im /
            ((j : ℝ) + 1))
        (hyperbolicModeIntegrand (fun t => Real.cosh (((j : ℝ) + 1) * t)) v (j + 2) ψ -
          hyperbolicModeIntegrand (fun t => Real.cosh ((j : ℝ) * t)) v (j + 1) ψ) ψ := by
    intro ψ _
    have h := (hasDerivAt_edge_antiderivative v j ψ).div_const ((j : ℝ) + 1)
    rwa [mul_div_cancel_left₀ _ hj] at h
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hF ((hc₁.sub hc₀).intervalIntegrable _ _)
  have hends : ∀ ψ : ℝ, Real.cos ψ = 0 →
      (hyperbolicKernelPoint v ψ ^ (j + 1) * (Real.sinh (((j : ℝ) + 1) * hyperbolicAngle v ψ) : ℂ)).im = 0 := by
    intro ψ hψ
    simp [hyperbolicAngle, hψ, Real.arsinh_zero]
  have hneg : Real.cos (-(Real.pi / 2)) = 0 := by rw [Real.cos_neg]; exact Real.cos_pi_div_two
  rw [hends (Real.pi / 2) Real.cos_pi_div_two, hends (-(Real.pi / 2)) hneg,
    intervalIntegral.integral_sub (hc₁.intervalIntegrable _ _) (hc₀.intervalIntegrable _ _)] at hftc
  have hsub : hyperbolicMode (fun t => Real.cosh (((j : ℝ) + 1) * t)) v (j + 2) -
      hyperbolicMode (fun t => Real.cosh ((j : ℝ) * t)) v (j + 1) = 0 := by
    unfold hyperbolicMode
    simpa using hftc
  exact sub_eq_zero.mp hsub

private theorem chebyshevMode_succ_zero_add {v : ℝ} (hv : 0 < v) (n : ℤ) :
    chebyshevMode v (n + 1) 0 + chebyshevMode v (n - 1) 0 = 2 * chebyshevMode v n 1 := by
  unfold chebyshevMode
  rw [← intervalIntegral.integral_add ((continuous_chebyshevModeIntegrand hv _ _).intervalIntegrable _ _)
      ((continuous_chebyshevModeIntegrand hv _ _).intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [chebyshevModeIntegrand, pow_zero, Complex.one_re, pow_one, re_circleKernelPoint, mul_one]
  have hU := chebyshevU_eval_add_add_one n (Real.cos θ)
  linear_combination (Real.sin θ / Real.sqrt (Real.sin θ ^ 2 + v)) * hU

private theorem hyperbolicMode_add_hyperbolicMode_zero (v : ℝ) {κ₁ κ₀ κ : ℝ → ℝ}
    (hsum : ∀ t, κ₁ t + κ₀ t = 2 * Real.cosh t * κ t) (h₁ : Continuous κ₁) (h₀ : Continuous κ₀) :
    hyperbolicMode κ₁ v 0 + hyperbolicMode κ₀ v 0 = 2 * hyperbolicMode κ v 1 := by
  unfold hyperbolicMode
  rw [← intervalIntegral.integral_add ((continuous_hyperbolicModeIntegrand h₁ v _).intervalIntegrable _ _)
      ((continuous_hyperbolicModeIntegrand h₀ v _).intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun ψ _ => ?_
  simp only [hyperbolicModeIntegrand, pow_zero, Complex.one_re, pow_one, re_hyperbolicKernelPoint, mul_one]
  have hk := hsum (hyperbolicAngle v ψ)
  linear_combination (1 / Real.cosh (hyperbolicAngle v ψ)) * hk

private theorem sinhMode_succ_zero_add (v a : ℝ) :
    hyperbolicMode (fun t => Real.sinh ((a + 1) * t)) v 0 + hyperbolicMode (fun t => Real.sinh ((a - 1) * t)) v 0 =
      2 * hyperbolicMode (fun t => Real.sinh (a * t)) v 1 :=
  hyperbolicMode_add_hyperbolicMode_zero v (fun t => sinh_kernel_add a t) (by fun_prop) (by fun_prop)

private theorem coshMode_succ_zero_add (v a : ℝ) :
    hyperbolicMode (fun t => Real.cosh ((a + 1) * t)) v 0 + hyperbolicMode (fun t => Real.cosh ((a - 1) * t)) v 0 =
      2 * hyperbolicMode (fun t => Real.cosh (a * t)) v 1 :=
  hyperbolicMode_add_hyperbolicMode_zero v (fun t => cosh_kernel_add a t) (by fun_prop) (by fun_prop)

private theorem sinhKernel_cast_succ (k : ℕ) :
    (fun t => Real.sinh (((k + 1 : ℕ) : ℝ) * t)) = fun t => Real.sinh (((k : ℝ) + 1) * t) := by
  first | (ext t; push_cast; ring_nf) | (ext t; push_cast; done)

private theorem sinhKernel_cast_succ_succ (k : ℕ) :
    (fun t => Real.sinh (((k + 1 + 1 : ℕ) : ℝ) * t)) = fun t => Real.sinh (((k : ℝ) + 1 + 1) * t) := by
  first | (ext t; push_cast; ring_nf) | (ext t; push_cast; done)

private theorem sinhKernel_add_sub (k : ℕ) :
    (fun t => Real.sinh (((k : ℝ) + 1 - 1) * t)) = fun t => Real.sinh ((k : ℝ) * t) := by
  ext t
  ring_nf

private theorem coshKernel_cast_succ (k : ℕ) :
    (fun t => Real.cosh (((k + 1 : ℕ) : ℝ) * t)) = fun t => Real.cosh (((k : ℝ) + 1) * t) := by
  first | (ext t; push_cast; ring_nf) | (ext t; push_cast; done)

private theorem coshKernel_cast_succ_succ (k : ℕ) :
    (fun t => Real.cosh (((k + 1 + 1 : ℕ) : ℝ) * t)) = fun t => Real.cosh (((k : ℝ) + 1 + 1) * t) := by
  first | (ext t; push_cast; ring_nf) | (ext t; push_cast; done)

private theorem coshKernel_add_sub (k : ℕ) :
    (fun t => Real.cosh (((k : ℝ) + 1 - 1) * t)) = fun t => Real.cosh ((k : ℝ) * t) := by
  ext t
  ring_nf

private theorem chebyshevIndex_cast_succ (k : ℕ) : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega

private theorem chebyshevIndex_cast_succ_succ (k : ℕ) : ((k + 1 + 1 : ℕ) : ℤ) - 1 = (k : ℤ) + 1 := by omega

private theorem modes_cancel_pair {v : ℝ} (hv : 0 < v) (k : ℕ) :
    (∀ m : ℕ, (k + m) % 2 = 1 → k ≤ m →
        chebyshevMode v ((k : ℤ) - 1) m + hyperbolicMode (fun t => Real.sinh ((k : ℝ) * t)) v m = 0) ∧
      (∀ m : ℕ, (k + 1 + m) % 2 = 1 → k + 1 ≤ m →
        chebyshevMode v (((k + 1 : ℕ) : ℤ) - 1) m +
          hyperbolicMode (fun t => Real.sinh (((k + 1 : ℕ) : ℝ) * t)) v m = 0) := by
  induction k with
  | zero =>
    refine ⟨fun m _ _ => ?_, fun m hpar hle => ?_⟩
    · simp [chebyshevMode_neg_one, hyperbolicMode, hyperbolicModeIntegrand]
    · have hm : Even m := Nat.even_iff.mpr (by omega)
      have hm1 : 1 ≤ m := by omega
      simpa using chebyshevMode_zero_add_sinhMode_of_even hv hm hm1
  | succ k ih =>
    obtain ⟨ih₀, ih₁⟩ := ih
    rw [chebyshevIndex_cast_succ, sinhKernel_cast_succ] at ih₁
    refine ⟨?_, ?_⟩
    · intro m hpar hle
      rw [chebyshevIndex_cast_succ, sinhKernel_cast_succ]
      exact ih₁ m hpar hle
    · intro m hpar hle
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [chebyshevIndex_cast_succ_succ, sinhKernel_cast_succ_succ]
      have hA := chebyshevMode_add_chebyshevMode hv (k : ℤ) m'
      have hS := sinhMode_add_sinhMode hv ((k : ℝ) + 1) m'
      rw [sinhKernel_add_sub] at hS
      have h₁ := ih₁ (m' + 2) (by omega) (by omega)
      have h₂ := ih₁ m' (by omega) (by omega)
      have h₃ := ih₀ (m' + 1) (by omega) (by omega)
      linear_combination hA + hS - h₃ + h₁ + (1 + v) * h₂

private theorem modes_cancel_of_le {v : ℝ} (hv : 0 < v) (k m : ℕ) (hpar : (k + m) % 2 = 1) (hle : k ≤ m) :
    chebyshevMode v ((k : ℤ) - 1) m + hyperbolicMode (fun t => Real.sinh ((k : ℝ) * t)) v m = 0 :=
  (modes_cancel_pair hv k).1 m hpar hle

private theorem modes_cosh_pair {v : ℝ} (hv : 0 < v) (k : ℕ) :
    (∀ m : ℕ, (k + m) % 2 = 1 → m + 1 ≤ k →
        chebyshevMode v ((k : ℤ) - 1) m + hyperbolicMode (fun t => Real.sinh ((k : ℝ) * t)) v m =
          hyperbolicMode (fun t => Real.cosh ((k : ℝ) * t)) v m) ∧
      (∀ m : ℕ, (k + 1 + m) % 2 = 1 → m + 1 ≤ k + 1 →
        chebyshevMode v (((k + 1 : ℕ) : ℤ) - 1) m +
            hyperbolicMode (fun t => Real.sinh (((k + 1 : ℕ) : ℝ) * t)) v m =
          hyperbolicMode (fun t => Real.cosh (((k + 1 : ℕ) : ℝ) * t)) v m) := by
  induction k with
  | zero =>
    refine ⟨fun m _ hle => ?_, fun m hpar hle => ?_⟩
    · omega
    · obtain rfl : m = 0 := by omega
      simpa using chebyshevMode_zero_add_sinhMode_zero hv
  | succ k ih =>
    obtain ⟨ih₀, ih₁⟩ := ih
    rw [chebyshevIndex_cast_succ, sinhKernel_cast_succ, coshKernel_cast_succ] at ih₁
    refine ⟨?_, ?_⟩
    · intro m hpar hle
      rw [chebyshevIndex_cast_succ, sinhKernel_cast_succ, coshKernel_cast_succ]
      exact ih₁ m hpar hle
    · intro m hpar hle
      rw [chebyshevIndex_cast_succ_succ, sinhKernel_cast_succ_succ, coshKernel_cast_succ_succ]
      rcases m with _ | m'
      ·
        have hA := chebyshevMode_succ_zero_add hv (k : ℤ)
        have hS := sinhMode_succ_zero_add v ((k : ℝ) + 1)
        have hC := coshMode_succ_zero_add v ((k : ℝ) + 1)
        rw [sinhKernel_add_sub] at hS
        rw [coshKernel_add_sub] at hC
        have h₁ := ih₁ 1 (by omega) (by omega)
        have h₀ := ih₀ 0 (by omega) (by omega)
        linear_combination hA + hS - hC - h₀ + 2 * h₁
      · have hA := chebyshevMode_add_chebyshevMode hv (k : ℤ) m'
        have hS := sinhMode_add_sinhMode hv ((k : ℝ) + 1) m'
        have hC := coshMode_add_coshMode hv ((k : ℝ) + 1) m'
        rw [sinhKernel_add_sub] at hS
        rw [coshKernel_add_sub] at hC
        have h₂ := ih₁ m' (by omega) (by omega)
        rcases Nat.lt_or_ge (m' + 1) k with hlt | hge
        ·
          have h₁ := ih₁ (m' + 2) (by omega) (by omega)
          have h₃ := ih₀ (m' + 1) (by omega) (by omega)
          linear_combination hA + hS - hC - h₃ + h₁ + (1 + v) * h₂
        ·
          have hdiag : m' = k := by omega
          rw [hdiag] at hA hS hC h₂ ⊢
          have hK₁ := modes_cancel_of_le hv (k + 1) (k + 2) (by omega) (by omega)
          rw [chebyshevIndex_cast_succ, sinhKernel_cast_succ] at hK₁
          have hK₀ := modes_cancel_of_le hv k (k + 1) (by omega) (by omega)
          have hedge := coshMode_edge v k
          linear_combination hA + hS - hC - hK₀ + hK₁ + (1 + v) * h₂ - hedge

private theorem modes_eq_cosh_of_succ_le {v : ℝ} (hv : 0 < v) (k m : ℕ) (hpar : (k + m) % 2 = 1) (hle : m + 1 ≤ k) :
    chebyshevMode v ((k : ℤ) - 1) m + hyperbolicMode (fun t => Real.sinh ((k : ℝ) * t)) v m =
      hyperbolicMode (fun t => Real.cosh ((k : ℝ) * t)) v m :=
  (modes_cosh_pair hv k).1 m hpar hle

private theorem chebyshevMode_add_sinhMode_modes (n m : ℕ) (hnm : 2 ∣ n + m) {v : ℝ} (hv : 0 < v) :
    (n < m → chebyshevMode v n m + hyperbolicMode (fun t => Real.sinh (((n : ℝ) + 1) * t)) v m = 0) ∧
      (m ≤ n → chebyshevMode v n m + hyperbolicMode (fun t => Real.sinh (((n : ℝ) + 1) * t)) v m =
        hyperbolicMode (fun t => Real.cosh (((n : ℝ) + 1) * t)) v m) := by
  obtain ⟨c, hc⟩ := hnm
  refine ⟨fun hlt => ?_, fun hle => ?_⟩
  · have h := modes_cancel_of_le hv (n + 1) m (by omega) (by omega)
    rwa [chebyshevIndex_cast_succ, sinhKernel_cast_succ] at h
  · have h := modes_eq_cosh_of_succ_le hv (n + 1) m (by omega) (by omega)
    rwa [chebyshevIndex_cast_succ, sinhKernel_cast_succ, coshKernel_cast_succ] at h

namespace AutomorphicForm p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff weyl_mem_rowIsometrySubgroup₀ firstRowℂ archWeightOneℝ archWeightCharℝ archWeightOneℝ_weyl" namespace GL2Real p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform discreteSeriesPairing" end AutomorphicForm.GL2Real
p2m_open_scoped "AutomorphicForm AutomorphicForm.GL2Real" in
private theorem AutomorphicForm.GL2Real.chebyshevMode_add_sinhMode_of_two_dvd (n m : ℕ) (hnm : 2 ∣ n + m) (v : ℝ)
    (hv : 0 < v) :
    (n < m →
      (∫ θ in (0 : ℝ)..Real.pi,
          (Polynomial.Chebyshev.U ℝ n).eval (Real.cos θ) *
              (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
            Real.sqrt (Real.sin θ ^ 2 + v)) +
        (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.sinh (((n : ℝ) + 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
              (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                  ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
            Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ))) = 0) ∧
    (m ≤ n →
      (∫ θ in (0 : ℝ)..Real.pi,
          (Polynomial.Chebyshev.U ℝ n).eval (Real.cos θ) *
              (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
            Real.sqrt (Real.sin θ ^ 2 + v)) +
        (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.sinh (((n : ℝ) + 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
              (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                  ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
            Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ))) =
        ∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.cosh (((n : ℝ) + 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
              (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                  ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
            Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ))) := by
  exact chebyshevMode_add_sinhMode_modes n m hnm hv

private noncomputable def normalizedProfile (F : ℝ → ℂ) (m : ℕ) (v : ℝ) : ℂ := F v / ((Real.sqrt (1 + v) : ℂ) ^ m)

private theorem continuousOn_normalizedProfile {F : ℝ → ℂ} (hF : ContinuousOn F (Set.Ici 0)) (m : ℕ) :
    ContinuousOn (normalizedProfile F m) (Set.Ici 0) := by
  have hden : Continuous fun v : ℝ => (Real.sqrt (1 + v) : ℂ) ^ m := by
    first
      | fun_prop
      | exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.add continuous_id))).pow m
  have h : ContinuousOn (fun v : ℝ => F v / (Real.sqrt (1 + v) : ℂ) ^ m) (Set.Ici 0) := by
    refine hF.div₀ hden.continuousOn fun v hv => pow_ne_zero m (Complex.ofReal_ne_zero.mpr ?_)
    exact (Real.sqrt_pos.mpr (by linarith [Set.mem_Ici.mp hv])).ne'
  exact h

private theorem normalizedProfile_eq_zero {F : ℝ → ℂ} (m : ℕ) {v : ℝ} (h : F v = 0) : normalizedProfile F m v = 0 := by
  simp [normalizedProfile, h]

private theorem profile_integrand_eq (F : ℝ → ℂ) (m : ℕ) (t w : ℝ) :
    (((Real.cosh t : ℂ) + (w : ℂ) * Complex.I) / (Real.sqrt (1 + (Real.sinh t ^ 2 + w ^ 2)) : ℂ)) ^ m *
        F (Real.sinh t ^ 2 + w ^ 2) =
      ((Real.cosh t : ℂ) + (w : ℂ) * Complex.I) ^ m * normalizedProfile F m (Real.sinh t ^ 2 + w ^ 2) := by
  unfold normalizedProfile
  rw [div_pow]
  ring

private theorem integral_profile_comp_div {r : ℝ} (hr : 0 < r) (F : ℝ → ℂ) (m : ℕ) (t : ℝ) :
    (∫ u : ℝ, (((Real.cosh t : ℂ) + ((u / (2 * r) : ℝ) : ℂ) * Complex.I) /
          (Real.sqrt (1 + (Real.sinh t ^ 2 + (u / (2 * r)) ^ 2)) : ℂ)) ^ m *
        F (Real.sinh t ^ 2 + (u / (2 * r)) ^ 2)) =
      (2 * r : ℝ) •
        ∫ w : ℝ, ((Real.cosh t : ℂ) + (w : ℂ) * Complex.I) ^ m * normalizedProfile F m (Real.sinh t ^ 2 + w ^ 2) := by
  have h : (∫ u : ℝ, (((Real.cosh t : ℂ) + ((u / (2 * r) : ℝ) : ℂ) * Complex.I) /
          (Real.sqrt (1 + (Real.sinh t ^ 2 + (u / (2 * r)) ^ 2)) : ℂ)) ^ m *
        F (Real.sinh t ^ 2 + (u / (2 * r)) ^ 2)) =
      |2 * r| • ∫ w : ℝ, (((Real.cosh t : ℂ) + (w : ℂ) * Complex.I) /
          (Real.sqrt (1 + (Real.sinh t ^ 2 + w ^ 2)) : ℂ)) ^ m * F (Real.sinh t ^ 2 + w ^ 2) :=
    MeasureTheory.Measure.integral_comp_div
      (fun w : ℝ => (((Real.cosh t : ℂ) + (w : ℂ) * Complex.I) / (Real.sqrt (1 + (Real.sinh t ^ 2 + w ^ 2)) : ℂ)) ^ m *
        F (Real.sinh t ^ 2 + w ^ 2)) (2 * r)
  rw [h, abs_of_pos (by positivity : (0 : ℝ) < 2 * r)]
  congr 1
  congr 1
  funext w
  exact profile_integrand_eq F m t w

private theorem integral_mul_smul_integral_eq (κ : ℝ → ℝ) (c : ℝ) (G : ℝ → ℂ) (m : ℕ) :
    (∫ t : ℝ, ((κ |t| : ℝ) : ℂ) *
        (c • ∫ w : ℝ, ((Real.cosh t : ℂ) + (w : ℂ) * Complex.I) ^ m * G (Real.sinh t ^ 2 + w ^ 2))) =
      c • ∫ t : ℝ, ((κ |t| : ℝ) : ℂ) *
        ∫ w : ℝ, ((Real.cosh t : ℂ) + (w : ℂ) * Complex.I) ^ m * G (Real.sinh t ^ 2 + w ^ 2) := by
  rw [← MeasureTheory.integral_smul]
  congr 1
  funext t
  first
    | exact mul_smul_comm _ _ _
    | (simp only [Complex.real_smul]; ring)

private noncomputable def planeIntegrand (κ : ℝ → ℝ) (G : ℝ → ℂ) (m : ℕ) (p : ℝ × ℝ) : ℂ :=
  ((κ |Real.arsinh p.1| / Real.cosh (Real.arsinh p.1) : ℝ) : ℂ) *
    (((Real.cosh (Real.arsinh p.1) : ℂ) + (p.2 : ℂ) * Complex.I) ^ m * G (p.1 ^ 2 + p.2 ^ 2))

private theorem cosh_smul_integral_planeIntegrand (κ : ℝ → ℝ) (G : ℝ → ℂ) (m : ℕ) (t : ℝ) :
    |Real.cosh t| • (∫ w : ℝ, planeIntegrand κ G m (Real.sinh t, w)) =
      ((κ |t| : ℝ) : ℂ) * ∫ w : ℝ, ((Real.cosh t : ℂ) + (w : ℂ) * Complex.I) ^ m * G (Real.sinh t ^ 2 + w ^ 2) := by
  rw [abs_of_pos (Real.cosh_pos t), Complex.real_smul, ← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_const_mul]
  congr 1
  funext w
  simp only [planeIntegrand, Real.arsinh_sinh]
  have hc : (Real.cosh t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos t).ne'
  rw [Complex.ofReal_div]
  first | (field_simp; done) | (field_simp; ring)

private theorem integral_kernel_eq_integral_planeIntegrand (κ : ℝ → ℝ) (G : ℝ → ℂ) (m : ℕ) :
    (∫ t : ℝ, ((κ |t| : ℝ) : ℂ) *
        ∫ w : ℝ, ((Real.cosh t : ℂ) + (w : ℂ) * Complex.I) ^ m * G (Real.sinh t ^ 2 + w ^ 2)) =
      ∫ s : ℝ, ∫ w : ℝ, planeIntegrand κ G m (s, w) := by
  have himg : (∫ s in Real.sinh '' Set.univ, ∫ w : ℝ, planeIntegrand κ G m (s, w)) =
      ∫ t in Set.univ, |Real.cosh t| • ∫ w : ℝ, planeIntegrand κ G m (Real.sinh t, w) :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun t _ => (Real.hasDerivAt_sinh t).hasDerivWithinAt) (fun x _ y _ hxy => Real.sinh_injective hxy) _
  simp only [Set.image_univ, Set.range_eq_univ.mpr Real.sinh_surjective, MeasureTheory.setIntegral_univ] at himg
  rw [himg]
  congr 1
  funext t
  exact (cosh_smul_integral_planeIntegrand κ G m t).symm

private theorem continuous_planeIntegrand {κ : ℝ → ℝ} (hκ : Continuous κ) {G : ℝ → ℂ}
    (hG : ContinuousOn G (Set.Ici 0)) (m : ℕ) : Continuous (planeIntegrand κ G m) := by
  have hang : Continuous fun p : ℝ × ℝ => Real.arsinh p.1 := Real.continuous_arsinh.comp continuous_fst
  have h₁ : Continuous fun p : ℝ × ℝ => κ |Real.arsinh p.1| / Real.cosh (Real.arsinh p.1) :=
    (hκ.comp (continuous_abs.comp hang)).div₀ (Real.continuous_cosh.comp hang) fun _ => (Real.cosh_pos _).ne'
  have h₂ : Continuous fun p : ℝ × ℝ => ((Real.cosh (Real.arsinh p.1) : ℂ) + (p.2 : ℂ) * Complex.I) ^ m := by
    first
      | fun_prop
      | exact ((Complex.continuous_ofReal.comp (Real.continuous_cosh.comp hang)).add
          ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)).pow m
  have h₃ : Continuous fun p : ℝ × ℝ => G (p.1 ^ 2 + p.2 ^ 2) :=
    hG.comp_continuous ((continuous_fst.pow 2).add (continuous_snd.pow 2)) fun p => by
      show (0 : ℝ) ≤ p.1 ^ 2 + p.2 ^ 2
      positivity
  unfold planeIntegrand
  exact (Complex.continuous_ofReal.comp h₁).mul (h₂.mul h₃)

private theorem planeIntegrand_eq_zero_of_le {κ : ℝ → ℝ} {G : ℝ → ℂ} {V : ℝ} (hGs : ∀ v, V ≤ v → G v = 0) (m : ℕ)
    {p : ℝ × ℝ} (hp : V ≤ p.1 ^ 2 + p.2 ^ 2) : planeIntegrand κ G m p = 0 := by
  simp [planeIntegrand, hGs _ hp]

private theorem integrable_planeIntegrand {κ : ℝ → ℝ} (hκ : Continuous κ) {G : ℝ → ℂ}
    (hG : ContinuousOn G (Set.Ici 0)) {V : ℝ} (hGs : ∀ v, V ≤ v → G v = 0) (m : ℕ) :
    MeasureTheory.Integrable (planeIntegrand κ G m) := by
  have hR0 : 0 ≤ Real.sqrt (max V 0) := Real.sqrt_nonneg _
  have hVR : V ≤ Real.sqrt (max V 0) ^ 2 := by
    rw [Real.sq_sqrt (le_max_right _ _)]
    exact le_max_left _ _
  have hK : IsCompact (Set.Icc (-Real.sqrt (max V 0)) (Real.sqrt (max V 0)) ×ˢ
      Set.Icc (-Real.sqrt (max V 0)) (Real.sqrt (max V 0))) := isCompact_Icc.prod isCompact_Icc
  have hon : MeasureTheory.IntegrableOn (planeIntegrand κ G m) _ :=
    (continuous_planeIntegrand hκ hG m).continuousOn.integrableOn_compact hK
  refine MeasureTheory.integrableOn_univ.mp (hon.of_forall_diff_eq_zero MeasurableSet.univ fun p hp => ?_)
  refine planeIntegrand_eq_zero_of_le hGs m ?_
  have hp' := hp.2
  simp only [Set.mem_prod, Set.mem_Icc, not_and_or, not_le] at hp'
  rcases hp' with (h | h) | (h | h) <;>
    nlinarith [sq_nonneg p.1, sq_nonneg p.2, sq_nonneg (p.1 + Real.sqrt (max V 0)),
      sq_nonneg (p.1 - Real.sqrt (max V 0)), sq_nonneg (p.2 + Real.sqrt (max V 0)),
      sq_nonneg (p.2 - Real.sqrt (max V 0))]

private theorem integral_integral_planeIntegrand_eq {κ : ℝ → ℝ} {G : ℝ → ℂ} {m : ℕ}
    (hint : MeasureTheory.Integrable (planeIntegrand κ G m)) :
    (∫ s : ℝ, ∫ w : ℝ, planeIntegrand κ G m (s, w)) = ∫ p : ℝ × ℝ, planeIntegrand κ G m p := by
  rw [MeasureTheory.Measure.volume_eq_prod] at hint ⊢
  exact (MeasureTheory.integral_prod _ hint).symm

private noncomputable def angularIntegrand (κ : ℝ → ℝ) (m : ℕ) (ρ φ : ℝ) : ℂ :=
  ((κ |Real.arsinh (ρ * Real.cos φ)| / Real.cosh (Real.arsinh (ρ * Real.cos φ)) : ℝ) : ℂ) *
    ((Real.cosh (Real.arsinh (ρ * Real.cos φ)) : ℂ) + ((ρ * Real.sin φ : ℝ) : ℂ) * Complex.I) ^ m

private theorem planeIntegrand_polar (κ : ℝ → ℝ) (G : ℝ → ℂ) (m : ℕ) (ρ φ : ℝ) :
    planeIntegrand κ G m (ρ * Real.cos φ, ρ * Real.sin φ) = angularIntegrand κ m ρ φ * G (ρ ^ 2) := by
  have hsq : (ρ * Real.cos φ) ^ 2 + (ρ * Real.sin φ) ^ 2 = ρ ^ 2 := by
    linear_combination ρ ^ 2 * Real.cos_sq_add_sin_sq φ
  simp only [planeIntegrand, angularIntegrand, hsq]
  ring

private theorem angularIntegrand_pi_sub (κ : ℝ → ℝ) (m : ℕ) (ρ φ : ℝ) :
    angularIntegrand κ m ρ (Real.pi - φ) = angularIntegrand κ m ρ φ := by
  first
    | (simp only [angularIntegrand, Real.cos_pi_sub, Real.sin_pi_sub, mul_neg, Real.arsinh_neg, abs_neg,
        Real.cosh_neg]; done)
    | (simp [angularIntegrand, Real.arsinh_neg]; done)

private theorem angularIntegrand_neg_pi_sub (κ : ℝ → ℝ) (m : ℕ) (ρ φ : ℝ) :
    angularIntegrand κ m ρ (-Real.pi - φ) = angularIntegrand κ m ρ φ := by
  rw [show -Real.pi - φ = -(φ + Real.pi) by ring]
  first
    | (simp only [angularIntegrand, Real.cos_neg, Real.sin_neg, Real.cos_add_pi, Real.sin_add_pi, neg_neg, mul_neg,
        Real.arsinh_neg, abs_neg, Real.cosh_neg]; done)
    | (simp [angularIntegrand, Real.arsinh_neg, Real.cos_add_pi, Real.sin_add_pi]; done)

private theorem continuous_angularIntegrand {κ : ℝ → ℝ} (hκ : Continuous κ) (m : ℕ) (ρ : ℝ) :
    Continuous (angularIntegrand κ m ρ) := by
  have hang : Continuous fun φ : ℝ => Real.arsinh (ρ * Real.cos φ) :=
    Real.continuous_arsinh.comp (continuous_const.mul Real.continuous_cos)
  have h₁ : Continuous fun φ : ℝ => κ |Real.arsinh (ρ * Real.cos φ)| / Real.cosh (Real.arsinh (ρ * Real.cos φ)) :=
    (hκ.comp (continuous_abs.comp hang)).div₀ (Real.continuous_cosh.comp hang) fun _ => (Real.cosh_pos _).ne'
  have h₂ : Continuous fun φ : ℝ =>
      ((Real.cosh (Real.arsinh (ρ * Real.cos φ)) : ℂ) + ((ρ * Real.sin φ : ℝ) : ℂ) * Complex.I) ^ m := by
    first
      | fun_prop
      | exact ((Complex.continuous_ofReal.comp (Real.continuous_cosh.comp hang)).add
          ((Complex.continuous_ofReal.comp (continuous_const.mul Real.continuous_sin)).mul continuous_const)).pow m
  unfold angularIntegrand
  exact (Complex.continuous_ofReal.comp h₁).mul h₂

private theorem integral_angularIntegrand_eq_two_mul {κ : ℝ → ℝ} (hκ : Continuous κ) (m : ℕ) (ρ : ℝ) :
    (∫ φ in (-Real.pi)..Real.pi, angularIntegrand κ m ρ φ) =
      2 * ∫ φ in (-(Real.pi / 2))..(Real.pi / 2), angularIntegrand κ m ρ φ := by
  have hI : ∀ a b : ℝ, IntervalIntegrable (angularIntegrand κ m ρ) MeasureTheory.volume a b := fun a b =>
    (continuous_angularIntegrand hκ m ρ).intervalIntegrable a b
  have hsplit : (∫ φ in (-Real.pi)..Real.pi, angularIntegrand κ m ρ φ) =
      (∫ φ in (-Real.pi)..(-(Real.pi / 2)), angularIntegrand κ m ρ φ) +
        ((∫ φ in (-(Real.pi / 2))..(Real.pi / 2), angularIntegrand κ m ρ φ) +
          ∫ φ in (Real.pi / 2)..Real.pi, angularIntegrand κ m ρ φ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI (-Real.pi) (-(Real.pi / 2)))
        (hI (-(Real.pi / 2)) Real.pi),
      ← intervalIntegral.integral_add_adjacent_intervals (hI (-(Real.pi / 2)) (Real.pi / 2))
        (hI (Real.pi / 2) Real.pi)]
  have hmid : (∫ φ in (-(Real.pi / 2))..(Real.pi / 2), angularIntegrand κ m ρ φ) =
      (∫ φ in (-(Real.pi / 2))..(0 : ℝ), angularIntegrand κ m ρ φ) +
        ∫ φ in (0 : ℝ)..(Real.pi / 2), angularIntegrand κ m ρ φ :=
    (intervalIntegral.integral_add_adjacent_intervals (hI (-(Real.pi / 2)) 0) (hI 0 (Real.pi / 2))).symm
  have hright : (∫ φ in (Real.pi / 2)..Real.pi, angularIntegrand κ m ρ φ) =
      ∫ φ in (0 : ℝ)..(Real.pi / 2), angularIntegrand κ m ρ φ := by
    have e : (∫ φ in (0 : ℝ)..(Real.pi / 2), angularIntegrand κ m ρ (Real.pi - φ)) =
        ∫ φ in (Real.pi - Real.pi / 2)..(Real.pi - 0), angularIntegrand κ m ρ φ := by
      first
        | exact intervalIntegral.integral_comp_sub_left _ _
        | exact intervalIntegral.integral_comp_sub_left _
    rw [show Real.pi - Real.pi / 2 = Real.pi / 2 by ring, sub_zero] at e
    rw [← e]
    exact intervalIntegral.integral_congr fun φ _ => angularIntegrand_pi_sub κ m ρ φ
  have hleft : (∫ φ in (-Real.pi)..(-(Real.pi / 2)), angularIntegrand κ m ρ φ) =
      ∫ φ in (-(Real.pi / 2))..(0 : ℝ), angularIntegrand κ m ρ φ := by
    have e : (∫ φ in (-(Real.pi / 2))..(0 : ℝ), angularIntegrand κ m ρ (-Real.pi - φ)) =
        ∫ φ in (-Real.pi - 0)..(-Real.pi - -(Real.pi / 2)), angularIntegrand κ m ρ φ := by
      first
        | exact intervalIntegral.integral_comp_sub_left _ _
        | exact intervalIntegral.integral_comp_sub_left _
    rw [sub_zero, show -Real.pi - -(Real.pi / 2) = -(Real.pi / 2) by ring] at e
    rw [← e]
    exact intervalIntegral.integral_congr fun φ _ => angularIntegrand_neg_pi_sub κ m ρ φ
  rw [hsplit, hright, hleft, hmid]
  ring

private noncomputable def oddModeIntegrand (κ : ℝ → ℝ) (v : ℝ) (m : ℕ) (ψ : ℝ) : ℝ :=
  κ (hyperbolicAngle v ψ) * (hyperbolicKernelPoint v ψ ^ m).im / Real.cosh (hyperbolicAngle v ψ)

private theorem continuous_oddModeIntegrand {κ : ℝ → ℝ} (hκ : Continuous κ) (v : ℝ) (m : ℕ) :
    Continuous (oddModeIntegrand κ v m) := by
  unfold oddModeIntegrand
  refine Continuous.div ?_ ?_ ?_
  · exact (hκ.comp (continuous_hyperbolicAngle v)).mul
      (Complex.continuous_im.comp ((continuous_hyperbolicKernelPoint v).pow m))
  · exact Real.continuous_cosh.comp (continuous_hyperbolicAngle v)
  · intro ψ
    exact (Real.cosh_pos _).ne'

private theorem hyperbolicAngle_neg (v ψ : ℝ) : hyperbolicAngle v (-ψ) = hyperbolicAngle v ψ := by
  simp only [hyperbolicAngle, Real.cos_neg]

private theorem hyperbolicKernelPoint_neg (v ψ : ℝ) :
    hyperbolicKernelPoint v (-ψ) = (starRingEnd ℂ) (hyperbolicKernelPoint v ψ) := by
  apply Complex.ext <;> simp [hyperbolicKernelPoint, hyperbolicAngle_neg, Real.sin_neg]

private theorem oddModeIntegrand_neg (κ : ℝ → ℝ) (v : ℝ) (m : ℕ) (ψ : ℝ) :
    oddModeIntegrand κ v m (-ψ) = -oddModeIntegrand κ v m ψ := by
  have him : (hyperbolicKernelPoint v (-ψ) ^ m).im = -(hyperbolicKernelPoint v ψ ^ m).im := by
    rw [hyperbolicKernelPoint_neg]
    first
      | (rw [← map_pow, Complex.conj_im])
      | (simp [← map_pow])
  unfold oddModeIntegrand
  rw [hyperbolicAngle_neg, him]
  ring

private theorem integral_oddModeIntegrand (κ : ℝ → ℝ) (v : ℝ) (m : ℕ) :
    (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2), oddModeIntegrand κ v m ψ) = 0 := by
  have h₁ : (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2), oddModeIntegrand κ v m (-ψ)) =
      ∫ ψ in (-(Real.pi / 2))..(-(-(Real.pi / 2))), oddModeIntegrand κ v m ψ := by
    first
      | exact intervalIntegral.integral_comp_neg _
      | exact intervalIntegral.integral_comp_neg
  rw [neg_neg] at h₁
  have h₂ : (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2), oddModeIntegrand κ v m (-ψ)) =
      ∫ ψ in (-(Real.pi / 2))..(Real.pi / 2), -oddModeIntegrand κ v m ψ :=
    intervalIntegral.integral_congr fun ψ _ => oddModeIntegrand_neg κ v m ψ
  rw [intervalIntegral.integral_neg] at h₂
  linarith

private theorem angularIntegrand_eq_of_mem {κ : ℝ → ℝ} (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) {φ : ℝ}
    (hφ : φ ∈ Set.uIcc (-(Real.pi / 2)) (Real.pi / 2)) :
    angularIntegrand κ m ρ φ =
      ((hyperbolicModeIntegrand κ (ρ ^ 2) m φ : ℝ) : ℂ) + ((oddModeIntegrand κ (ρ ^ 2) m φ : ℝ) : ℂ) * Complex.I := by
  have hcos : 0 ≤ Real.cos φ := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hφ
    exact Real.cos_nonneg_of_mem_Icc hφ
  have habs : |Real.arsinh (ρ * Real.cos φ)| = Real.arsinh (ρ * Real.cos φ) :=
    abs_of_nonneg (Real.arsinh_nonneg_iff.mpr (mul_nonneg hρ.le hcos))
  have hangle : hyperbolicAngle (ρ ^ 2) φ = Real.arsinh (ρ * Real.cos φ) := by
    simp only [hyperbolicAngle, Real.sqrt_sq hρ.le]
  have hZ : hyperbolicKernelPoint (ρ ^ 2) φ =
      (Real.cosh (Real.arsinh (ρ * Real.cos φ)) : ℂ) + ((ρ * Real.sin φ : ℝ) : ℂ) * Complex.I := by
    simp only [hyperbolicKernelPoint, hangle, Real.sqrt_sq hρ.le]
  simp only [angularIntegrand, hyperbolicModeIntegrand, oddModeIntegrand, hangle, hZ, habs]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem integral_angularIntegrand_half {κ : ℝ → ℝ} (hκ : Continuous κ) (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ φ in (-(Real.pi / 2))..(Real.pi / 2), angularIntegrand κ m ρ φ) = ((hyperbolicMode κ (ρ ^ 2) m : ℝ) : ℂ) := by
  have hA : IntervalIntegrable (fun φ : ℝ => ((hyperbolicModeIntegrand κ (ρ ^ 2) m φ : ℝ) : ℂ)) MeasureTheory.volume
      (-(Real.pi / 2)) (Real.pi / 2) :=
    (Complex.continuous_ofReal.comp (continuous_hyperbolicModeIntegrand hκ _ _)).intervalIntegrable _ _
  have hB : IntervalIntegrable (fun φ : ℝ => ((oddModeIntegrand κ (ρ ^ 2) m φ : ℝ) : ℂ) * Complex.I)
      MeasureTheory.volume (-(Real.pi / 2)) (Real.pi / 2) :=
    ((Complex.continuous_ofReal.comp (continuous_oddModeIntegrand hκ _ _)).mul continuous_const).intervalIntegrable _ _
  have hre : (∫ φ in (-(Real.pi / 2))..(Real.pi / 2), ((hyperbolicModeIntegrand κ (ρ ^ 2) m φ : ℝ) : ℂ)) =
      ((∫ φ in (-(Real.pi / 2))..(Real.pi / 2), hyperbolicModeIntegrand κ (ρ ^ 2) m φ : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  have him : (∫ φ in (-(Real.pi / 2))..(Real.pi / 2), ((oddModeIntegrand κ (ρ ^ 2) m φ : ℝ) : ℂ)) =
      ((∫ φ in (-(Real.pi / 2))..(Real.pi / 2), oddModeIntegrand κ (ρ ^ 2) m φ : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  unfold hyperbolicMode
  rw [intervalIntegral.integral_congr fun φ hφ => angularIntegrand_eq_of_mem m hρ hφ,
    intervalIntegral.integral_add hA hB, intervalIntegral.integral_mul_const, hre, him, integral_oddModeIntegrand,
    Complex.ofReal_zero, zero_mul, add_zero]

private noncomputable def radialIntegrand (κ : ℝ → ℝ) (G : ℝ → ℂ) (m : ℕ) (v : ℝ) : ℂ :=
  G v * ((hyperbolicMode κ v m : ℝ) : ℂ)

private theorem setIntegral_polar_slice {κ : ℝ → ℝ} (hκ : Continuous κ) (G : ℝ → ℂ) (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ φ in Set.Ioo (-Real.pi) Real.pi, ρ • planeIntegrand κ G m (ρ * Real.cos φ, ρ * Real.sin φ)) =
      |2 * ρ| • radialIntegrand κ G m (ρ ^ 2) := by
  have hle : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle]
  simp_rw [planeIntegrand_polar]
  rw [intervalIntegral.integral_smul, intervalIntegral.integral_mul_const, integral_angularIntegrand_eq_two_mul hκ,
    integral_angularIntegrand_half hκ m hρ, abs_of_pos (by positivity : (0 : ℝ) < 2 * ρ), radialIntegrand]
  simp only [Complex.real_smul]
  first | (push_cast; ring) | (push_cast; done)

private noncomputable def polarIntegrand (κ : ℝ → ℝ) (G : ℝ → ℂ) (m : ℕ) (p : ℝ × ℝ) : ℂ :=
  p.1 • planeIntegrand κ G m (p.1 * Real.cos p.2, p.1 * Real.sin p.2)

private theorem continuous_polarIntegrand {κ : ℝ → ℝ} (hκ : Continuous κ) {G : ℝ → ℂ}
    (hG : ContinuousOn G (Set.Ici 0)) (m : ℕ) : Continuous (polarIntegrand κ G m) := by
  have hmap : Continuous fun p : ℝ × ℝ => (p.1 * Real.cos p.2, p.1 * Real.sin p.2) := by
    first
      | fun_prop
      | exact (continuous_fst.mul (Real.continuous_cos.comp continuous_snd)).prodMk
          (continuous_fst.mul (Real.continuous_sin.comp continuous_snd))
  unfold polarIntegrand
  exact continuous_fst.smul ((continuous_planeIntegrand hκ hG m).comp hmap)

private theorem integrableOn_polarIntegrand {κ : ℝ → ℝ} (hκ : Continuous κ) {G : ℝ → ℂ}
    (hG : ContinuousOn G (Set.Ici 0)) {V : ℝ} (hGs : ∀ v, V ≤ v → G v = 0) (m : ℕ) :
    MeasureTheory.IntegrableOn (polarIntegrand κ G m) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  have hRnn : 0 ≤ Real.sqrt (max V 0) := Real.sqrt_nonneg _
  have hVR : V ≤ Real.sqrt (max V 0) ^ 2 := by
    rw [Real.sq_sqrt (le_max_right _ _)]
    exact le_max_left _ _
  have hK : IsCompact (Set.Icc (0 : ℝ) (Real.sqrt (max V 0)) ×ˢ Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hon : MeasureTheory.IntegrableOn (polarIntegrand κ G m) _ :=
    (continuous_polarIntegrand hκ hG m).continuousOn.integrableOn_compact hK
  refine hon.of_forall_diff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
  obtain ⟨hps, hpK⟩ := hp
  obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hps
  have hp1' : 0 < p.1 := Set.mem_Ioi.mp hp1
  have hp2' := Set.mem_Ioo.mp hp2
  have hR : Real.sqrt (max V 0) < p.1 := by
    by_contra hcon
    push_neg at hcon
    exact hpK (Set.mem_prod.mpr ⟨Set.mem_Icc.mpr ⟨hp1'.le, hcon⟩, Set.mem_Icc.mpr ⟨hp2'.1.le, hp2'.2.le⟩⟩)
  unfold polarIntegrand
  rw [planeIntegrand_polar, hGs (p.1 ^ 2) (by nlinarith), mul_zero, smul_zero]

private theorem integral_planeIntegrand_eq_integral_radial {κ : ℝ → ℝ} (hκ : Continuous κ) {G : ℝ → ℂ}
    (hG : ContinuousOn G (Set.Ici 0)) {V : ℝ} (hGs : ∀ v, V ≤ v → G v = 0) (m : ℕ) :
    (∫ p : ℝ × ℝ, planeIntegrand κ G m p) = ∫ ρ in Set.Ioi (0 : ℝ), |2 * ρ| • radialIntegrand κ G m (ρ ^ 2) := by
  have hpolar : (∫ p : ℝ × ℝ, planeIntegrand κ G m p) = ∫ p in polarCoord.target, polarIntegrand κ G m p := by
    first
      | exact (integral_comp_polarCoord_symm (planeIntegrand κ G m)).symm
      | (rw [← integral_comp_polarCoord_symm (planeIntegrand κ G m)]; rfl)
  have htarget : polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi := by
    first | rfl | (simp [polarCoord]; done)
  have hint : MeasureTheory.IntegrableOn (polarIntegrand κ G m) (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    first
      | exact integrableOn_polarIntegrand hκ hG hGs m
      | (rw [← MeasureTheory.Measure.volume_eq_prod]; exact integrableOn_polarIntegrand hκ hG hGs m)
  rw [hpolar, htarget, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.setIntegral_prod _ hint]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  exact setIntegral_polar_slice hκ G m (Set.mem_Ioi.mp hρ)

private theorem integral_abs_two_mul_smul_eq (H : ℝ → ℂ) :
    (∫ ρ in Set.Ioi (0 : ℝ), |2 * ρ| • H (ρ ^ 2)) = ∫ v in Set.Ioi (0 : ℝ), H v := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt (fun x : ℝ => x ^ 2) (2 * x) (Set.Ioi 0) x := fun x _ => by
    first
      | exact (hasDerivAt_pow 2 x).hasDerivWithinAt.congr_deriv (by norm_num)
      | simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have hinj : Set.InjOn (fun x : ℝ => x ^ 2) (Set.Ioi 0) := by
    intro x hx y hy hxy
    have h' : x ^ 2 = y ^ 2 := hxy
    calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq (Set.mem_Ioi.mp hx).le).symm
      _ = Real.sqrt (y ^ 2) := by rw [h']
      _ = y := Real.sqrt_sq (Set.mem_Ioi.mp hy).le
  have himg : (∫ v in (fun x : ℝ => x ^ 2) '' Set.Ioi 0, H v) = ∫ ρ in Set.Ioi (0 : ℝ), |2 * ρ| • H (ρ ^ 2) :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj H
  have hset : (fun x : ℝ => x ^ 2) '' Set.Ioi 0 = Set.Ioi 0 := by
    ext v
    constructor
    · rintro ⟨ρ, hρ, rfl⟩
      exact pow_pos (Set.mem_Ioi.mp hρ) 2
    · intro hv
      exact ⟨Real.sqrt v, Real.sqrt_pos.mpr (Set.mem_Ioi.mp hv), Real.sq_sqrt (Set.mem_Ioi.mp hv).le⟩
  rw [hset] at himg
  exact himg.symm

private theorem integral_kernel_mul_integral_profile_eq (m : ℕ) {r : ℝ} (hr : 0 < r) {κ : ℝ → ℝ} (hκ : Continuous κ)
    {F : ℝ → ℂ} (hF : ContinuousOn F (Set.Ici 0)) (hFs : ∃ V : ℝ, ∀ v, V ≤ v → F v = 0) :
    (∫ t : ℝ, ((κ |t| : ℝ) : ℂ) *
        ∫ u : ℝ, (((Real.cosh t : ℂ) + ((u / (2 * r) : ℝ) : ℂ) * Complex.I) /
              (Real.sqrt (1 + (Real.sinh t ^ 2 + (u / (2 * r)) ^ 2)) : ℂ)) ^ m *
          F (Real.sinh t ^ 2 + (u / (2 * r)) ^ 2)) =
      2 * (r : ℂ) * ∫ v in Set.Ioi (0 : ℝ), F v / ((Real.sqrt (1 + v) : ℂ) ^ m) *
        ((∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
            κ (Real.arsinh (Real.sqrt v * Real.cos ψ)) *
                (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                    ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
              Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℝ) : ℂ) := by
  obtain ⟨V, hFV⟩ := hFs
  have hG : ContinuousOn (normalizedProfile F m) (Set.Ici 0) := continuousOn_normalizedProfile hF m
  have hGs : ∀ v, V ≤ v → normalizedProfile F m v = 0 := fun v hv => normalizedProfile_eq_zero m (hFV v hv)
  simp only [integral_profile_comp_div hr F m]
  rw [integral_mul_smul_integral_eq, integral_kernel_eq_integral_planeIntegrand,
    integral_integral_planeIntegrand_eq (integrable_planeIntegrand hκ hG hGs m),
    integral_planeIntegrand_eq_integral_radial hκ hG hGs m, integral_abs_two_mul_smul_eq, Complex.real_smul]
  show ((2 * r : ℝ) : ℂ) * (∫ v in Set.Ioi (0 : ℝ), radialIntegrand κ (normalizedProfile F m) m v) =
    2 * (r : ℂ) * ∫ v in Set.Ioi (0 : ℝ), radialIntegrand κ (normalizedProfile F m) m v
  first | (push_cast; ring) | (push_cast; done) | (rw [Complex.ofReal_mul, Complex.ofReal_ofNat])

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff weyl_mem_rowIsometrySubgroup₀ firstRowℂ archWeightOneℝ archWeightCharℝ archWeightOneℝ_weyl"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform discreteSeriesPairing"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

open MeasureTheory

section

variable {f : GL (Fin 2) ℝ → ℂ} {m : ℕ}

private theorem upperTriangular_neg_neg (a₁ a₂ u : ℝ) (h : a₁ * a₂ ≠ 0) (h' : -a₁ * -a₂ ≠ 0) :
    upperTriangular (-a₁) (-a₂) u h' = -upperTriangular a₁ a₂ (-u) h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [upperTriangular]

private theorem ellipticElt_pi_sub (r θ : ℝ) (hr : 0 < r) :
    ellipticElt r (Real.pi - θ) hr = -ellipticElt r (-θ) hr := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [ellipticElt, Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_neg, Real.sin_neg]

private theorem ellipticElt_neg_pi_sub (r θ : ℝ) (hr : 0 < r) :
    ellipticElt r (-(Real.pi - θ)) hr = -ellipticElt r θ hr := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [ellipticElt]

private theorem splitTransform_neg_neg (hf : ∀ g, f (-g) = (-1) ^ m * f g) (a₁ a₂ : ℝ) :
    splitTransform f (-a₁) (-a₂) = (-1) ^ m * splitTransform f a₁ a₂ := by
  unfold splitTransform
  by_cases h : a₁ * a₂ ≠ 0
  · have h' : -a₁ * -a₂ ≠ 0 := by rwa [neg_mul_neg]
    rw [dif_pos h', dif_pos h, mul_left_comm]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext θ
    rw [← integral_const_mul]
    simp_rw [upperTriangular_neg_neg a₁ a₂ _ h h', mul_neg, neg_mul, hf]
    exact integral_neg_eq_self
      (fun u : ℝ => (-1 : ℂ) ^ m * f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹)) volume
  · have h' : ¬ (-a₁ * -a₂ ≠ 0) := by rwa [neg_mul_neg]
    rw [dif_neg h', dif_neg h, mul_zero]

private theorem ellipticTransform_pi_sub (hf : ∀ g, f (-g) = (-1) ^ m * f g) (r θ : ℝ) :
    ellipticTransform f r (Real.pi - θ) = (-1) ^ m * ellipticTransform f r θ := by
  unfold ellipticTransform
  by_cases hr : 0 < r
  · rw [dif_pos hr, dif_pos hr, Real.sin_pi_sub, mul_left_comm]
    congr 1
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [← integral_const_mul]
    congr 1
    funext x
    by_cases hy : 0 < y
    · rw [dif_pos hy, dif_pos hy, ellipticElt_pi_sub, ellipticElt_neg_pi_sub, mul_neg, neg_mul, mul_neg,
        neg_mul, hf, hf]
      ring
    · rw [dif_neg hy, dif_neg hy, mul_zero]
  · rw [dif_neg hr, dif_neg hr, mul_zero]

private theorem chebyshevU_eval_neg_of_two_le {j : ℕ} (hj : 2 ≤ j) (c : ℝ) :
    (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (-c) =
      (-1) ^ j * (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval c := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 2 := ⟨j - 2, by omega⟩
  have hcast : ((n + 2 : ℕ) : ℤ) - 2 = (n : ℤ) := by push_cast; ring
  rw [hcast, Polynomial.Chebyshev.U_eval_neg, Int.cast_negOnePow_natCast, pow_add]
  ring

private theorem neg_one_pow_mul_neg_one_pow_of_not_two_dvd {j : ℕ} (hodd : ¬ 2 ∣ j + m) :
    (-1 : ℂ) ^ j * (-1 : ℂ) ^ m = -1 := by
  rw [← pow_add]
  rcases Nat.even_or_odd (j + m) with h | h
  · exact absurd (even_iff_two_dvd.mp h) hodd
  · exact h.neg_one_pow

private theorem intervalIntegral_ellipticTransform_mul_chebyshevU_eq_zero_of_not_two_dvd
    (hf : ∀ g, f (-g) = (-1) ^ m * f g) {j : ℕ} (hj : 2 ≤ j) (hodd : ¬ 2 ∣ j + m) (r : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
        ellipticTransform f r θ *
          (((Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) = 0 := by
  set F : ℝ → ℂ := fun θ =>
    ellipticTransform f r θ * (((Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ) with hF
  show (∫ θ in (0 : ℝ)..Real.pi, F θ) = 0
  have hsign : (-1 : ℂ) ^ m * (-1 : ℂ) ^ j = -1 := by
    rw [mul_comm]; exact neg_one_pow_mul_neg_one_pow_of_not_two_dvd hodd
  have hflip : ∀ θ : ℝ, F (Real.pi - θ) = -F θ := by
    intro θ
    simp only [hF]
    rw [ellipticTransform_pi_sub hf, Real.cos_pi_sub, chebyshevU_eval_neg_of_two_le hj, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]
    linear_combination
      (ellipticTransform f r θ *
        (((Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) * hsign
  have h1 : (∫ θ in (0 : ℝ)..Real.pi, F (Real.pi - θ)) = ∫ θ in (0 : ℝ)..Real.pi, F θ := by
    simp
  have h2 : (∫ θ in (0 : ℝ)..Real.pi, F θ) = -∫ θ in (0 : ℝ)..Real.pi, F θ := by
    calc (∫ θ in (0 : ℝ)..Real.pi, F θ) = ∫ θ in (0 : ℝ)..Real.pi, F (Real.pi - θ) := h1.symm
      _ = ∫ θ in (0 : ℝ)..Real.pi, -F θ := by simp_rw [hflip]
      _ = -∫ θ in (0 : ℝ)..Real.pi, F θ := intervalIntegral.integral_neg
  linear_combination (1 / 2 : ℂ) * h2

private theorem integral_mul_splitTransform_bracket_eq_zero_of_not_two_dvd (hf : ∀ g, f (-g) = (-1) ^ m * f g)
    {j : ℕ} (hodd : ¬ 2 ∣ j + m) (κ : ℝ → ℂ) (r : ℝ) :
    (∫ t : ℝ, κ t *
        (splitTransform f (r * Real.exp t) (r * Real.exp (-t)) +
          (-1 : ℂ) ^ j * splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t))))) = 0 := by
  have hsign := neg_one_pow_mul_neg_one_pow_of_not_two_dvd (m := m) hodd
  have hbr : ∀ t : ℝ, splitTransform f (r * Real.exp t) (r * Real.exp (-t)) +
      (-1 : ℂ) ^ j * splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t))) = 0 := by
    intro t
    rw [splitTransform_neg_neg hf]
    linear_combination (splitTransform f (r * Real.exp t) (r * Real.exp (-t))) * hsign
  simp_rw [hbr, mul_zero, integral_zero]

private theorem discreteSeriesPairing_eq_zero_of_not_two_dvd (hf : ∀ g, f (-g) = (-1) ^ m * f g) {j : ℕ} (hj : 2 ≤ j)
    (hodd : ¬ 2 ∣ j + m) (r : ℝ) :
    discreteSeriesPairing j (splitTransform f) (ellipticTransform f) r = 0 := by
  unfold discreteSeriesPairing
  rw [intervalIntegral_ellipticTransform_mul_chebyshevU_eq_zero_of_not_two_dvd hf hj hodd r,
    integral_mul_splitTransform_bracket_eq_zero_of_not_two_dvd hf hodd
      (fun t : ℝ => (Real.exp (-(((j : ℝ) - 1) * |t|)) : ℂ)) r]
  simp

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

private noncomputable def weylElt : rowIsometrySubgroup₀ ℝ := ⟨_, weyl_mem_rowIsometrySubgroup₀ ℝ⟩

private theorem coe_weylElt_mul_weylElt : ((weylElt * weylElt : rowIsometrySubgroup₀ ℝ) : GL (Fin 2) ℝ) = -1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [weylElt, Matrix.mul_apply, Fin.sum_univ_two]

private theorem archWeightChar_weylElt (m : ℕ) : ((archWeightCharℝ (m : ℤ) weylElt : ℂˣ) : ℂ) = Complex.I ^ m := by
  have h1 : ((archWeightOneℝ weylElt : ℂˣ) : ℂ) = Complex.I := archWeightOneℝ_weyl
  show (((archWeightOneℝ weylElt) ^ (m : ℤ) : ℂˣ) : ℂ) = Complex.I ^ m
  rw [Units.val_zpow_eq_zpow_val, zpow_natCast, h1]

private theorem apply_neg_eq_neg_one_pow_mul {m : ℕ} {f : GL (Fin 2) ℝ → ℂ}
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (g : GL (Fin 2) ℝ) : f (-g) = (-1) ^ m * f g := by
  have key := htype (weylElt * weylElt) 1 g
  rw [coe_weylElt_mul_weylElt, map_mul, Units.val_mul, archWeightChar_weylElt] at key
  simp only [map_one, Units.val_one, OneMemClass.coe_one, mul_one, neg_one_mul] at key
  rw [key, ← mul_pow, Complex.I_mul_I]

private noncomputable def diagonalElt (r : ℝ) (hr : 0 < r) (v : ℝ) : GL (Fin 2) ℝ :=
  upperTriangular (r * Real.exp (Real.arsinh (Real.sqrt v))) (r * Real.exp (-Real.arsinh (Real.sqrt v))) 0
    (by positivity)

private theorem coe_diagonalElt (r : ℝ) (hr : 0 < r) :
    ∀ v : ℝ, 0 ≤ v → ((diagonalElt r hr v : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * (Real.sqrt (1 + v) + Real.sqrt v), 0; 0, r * (Real.sqrt (1 + v) - Real.sqrt v)] := by
  intro v hv
  have h1 : Real.exp (Real.arsinh (Real.sqrt v)) = Real.sqrt (1 + v) + Real.sqrt v := by
    rw [Real.exp_arsinh, Real.sq_sqrt hv, add_comm]
  have hprod : (Real.sqrt (1 + v) + Real.sqrt v) * (Real.sqrt (1 + v) - Real.sqrt v) = 1 := by
    rw [← sq_sub_sq, Real.sq_sqrt (show (0 : ℝ) ≤ 1 + v by linarith), Real.sq_sqrt hv]; ring
  have h2 : Real.exp (-Real.arsinh (Real.sqrt v)) = Real.sqrt (1 + v) - Real.sqrt v := by
    rw [Real.exp_neg, h1]; exact inv_eq_of_mul_eq_one_right hprod
  show !![r * Real.exp (Real.arsinh (Real.sqrt v)), (0 : ℝ); 0, r * Real.exp (-Real.arsinh (Real.sqrt v))] = _
  rw [h1, h2]

section ProfileHelper

p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.AutomorphicForm AutomorphicForm.WindowedSiegel"

namespace RotationTypeProfile

private noncomputable def rotationElt (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] (by
    rw [Matrix.det_fin_two_of]
    have h : Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ = 1 := by
      linear_combination Real.cos_sq_add_sin_sq (x := θ)
    rw [h]
    exact one_ne_zero)

private theorem rotationElt_val (θ : ℝ) :
    (rotationElt θ : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl

private theorem det_rotationElt (θ : ℝ) : (rotationElt θ : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [rotationElt_val, Matrix.det_fin_two_of]
  linear_combination Real.cos_sq_add_sin_sq (x := θ)

private theorem rotationElt_mem (θ : ℝ) : rotationElt θ ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨det_rotationElt θ, ?_⟩
  constructor
  · rw [det_rotationElt θ, norm_one]
  · intro u v
    rw [rotationElt_val]
    show ‖u * Real.cos θ + v * -Real.sin θ‖ ^ 2 + ‖u * Real.sin θ + v * Real.cos θ‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2
    simp only [Real.norm_eq_abs, sq_abs]
    linear_combination (u ^ 2 + v ^ 2) * Real.cos_sq_add_sin_sq (x := θ)

private theorem archWeightChar_rotationElt (m : ℕ) (θ : ℝ) :
    ((archWeightCharℝ (m : ℤ) ⟨rotationElt θ, rotationElt_mem θ⟩ : ℂˣ) : ℂ) =
      Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) := by
  have h1 : ((archWeightOneℝ ⟨rotationElt θ, rotationElt_mem θ⟩ : ℂˣ) : ℂ) =
      Complex.exp ((θ : ℂ) * Complex.I) := by
    show firstRowℂ (rotationElt θ) = _
    apply Complex.ext
    · simp [firstRowℂ, rotationElt_val, Complex.exp_ofReal_mul_I_re]
    · simp [firstRowℂ, rotationElt_val, Complex.exp_ofReal_mul_I_im]
  simp only [archWeightCharℝ, MonoidHom.comp_apply, zpowGroupHom_apply, zpow_natCast, Units.val_pow_eq_pow_val]
  rw [h1, ← Complex.exp_nat_mul]
  congr 1
  ring

private theorem norm_mul_cos_arg_eq_re (z : ℂ) : ‖z‖ * Real.cos (Complex.arg z) = z.re := by
  by_cases hz : z = 0
  · subst hz
    simp
  · have h : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [Complex.cos_arg hz, mul_div_assoc', mul_comm, mul_div_assoc, div_self h, mul_one]

private theorem norm_mul_sin_arg_eq_im (z : ℂ) : ‖z‖ * Real.sin (Complex.arg z) = z.im := by
  by_cases hz : z = 0
  · subst hz
    simp
  · have h : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [Complex.sin_arg, mul_div_assoc', mul_comm, mul_div_assoc, div_self h, mul_one]

private theorem normSq_sub_normSq_eq_det (g : GL (Fin 2) ℝ) :
    Complex.normSq
        (⟨((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2,
          ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2⟩ : ℂ) -
      Complex.normSq
        (⟨((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2,
          -(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2)⟩ : ℂ) =
      (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
  rw [Matrix.det_fin_two]
  simp only [Complex.normSq_apply]
  ring

private theorem apply_eq_exp_mul_arg_mul_apply_diagonal_of_weight (m : ℕ) (f : GL (Fin 2) ℝ → ℂ)
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (g : GL (Fin 2) ℝ) :
    let a : ℂ :=
      ⟨((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2,
        ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2⟩
    let b : ℂ :=
      ⟨((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2,
        -(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2)⟩
    ∀ d : GL (Fin 2) ℝ, (d : Matrix (Fin 2) (Fin 2) ℝ) = !![‖a‖ + ‖b‖, 0; 0, ‖a‖ - ‖b‖] →
      f g = Complex.exp ((m : ℂ) * (Complex.arg a : ℂ) * Complex.I) * f d := by
  intro a b d hd
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, φ = (Complex.arg a + Complex.arg b) / 2 := ⟨_, rfl⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℝ, ψ = (Complex.arg a - Complex.arg b) / 2 := ⟨_, rfl⟩
  have hargA : Complex.arg a = φ + ψ := by rw [hφ, hψ]; ring
  have hargB : Complex.arg b = φ - ψ := by rw [hφ, hψ]; ring
  have A1' := norm_mul_cos_arg_eq_re a
  have A2' := norm_mul_sin_arg_eq_im a
  have B1' := norm_mul_cos_arg_eq_re b
  have B2' := norm_mul_sin_arg_eq_im b
  rw [hargA] at A1' A2'
  rw [hargB] at B1' B2'
  rw [Real.cos_add] at A1'
  rw [Real.sin_add] at A2'
  rw [Real.cos_sub] at B1'
  rw [Real.sin_sub] at B2'
  have A1 : ‖a‖ * (Real.cos φ * Real.cos ψ - Real.sin φ * Real.sin ψ) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2 := A1'
  have A2 : ‖a‖ * (Real.sin φ * Real.cos ψ + Real.cos φ * Real.sin ψ) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2 := A2'
  have B1 : ‖b‖ * (Real.cos φ * Real.cos ψ + Real.sin φ * Real.sin ψ) =
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2 := B1'
  have B2 : ‖b‖ * (Real.sin φ * Real.cos ψ - Real.cos φ * Real.sin ψ) =
      -(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2) := B2'
  have hmat : (g : Matrix (Fin 2) (Fin 2) ℝ) =
      !![Real.cos φ, Real.sin φ; -Real.sin φ, Real.cos φ] * !![‖a‖ + ‖b‖, 0; 0, ‖a‖ - ‖b‖] *
        !![Real.cos ψ, Real.sin ψ; -Real.sin ψ, Real.cos ψ] := by
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> nlinarith [A1, A2, B1, B2]
  have hg : g = rotationElt φ * d * rotationElt ψ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, rotationElt_val, rotationElt_val, hd]
    exact hmat
  rw [hg]
  refine (htype ⟨rotationElt φ, rotationElt_mem φ⟩ ⟨rotationElt ψ, rotationElt_mem ψ⟩ d).trans ?_
  rw [archWeightChar_rotationElt, archWeightChar_rotationElt, ← Complex.exp_add, hargA]
  rw [show ((m : ℂ) * (φ : ℂ) * Complex.I + (m : ℂ) * (ψ : ℂ) * Complex.I) =
      (m : ℂ) * ((φ + ψ : ℝ) : ℂ) * Complex.I by push_cast; ring]

end RotationTypeProfile
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

end ProfileHelper
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

section EllipticSide

open MeasureTheory

private theorem continuous_generalLinearGroup_of_continuous_val {X : Type} [TopologicalSpace X] (D : X → GL (Fin 2) ℝ)
    (h : Continuous fun x => ((D x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)) : Continuous D := by
  refine Units.continuous_iff.mpr ⟨h, ?_⟩
  have hinv : (fun x => (((D x)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
      = fun x => (((D x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ •
          ((D x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).adjugate := by
    funext x
    rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv]
  rw [hinv]
  refine Continuous.smul (Continuous.inv₀ h.matrix_det fun x => ?_) h.matrix_adjugate
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (D x).isUnit).ne_zero

private theorem continuous_diagonalElt (r : ℝ) (hr : 0 < r) : Continuous (diagonalElt r hr) := by
  refine continuous_generalLinearGroup_of_continuous_val (diagonalElt r hr) ?_
  have he : Continuous fun v : ℝ => r * Real.exp (Real.arsinh (Real.sqrt v)) :=
    continuous_const.mul (Real.continuous_exp.comp (Real.continuous_arsinh.comp Real.continuous_sqrt))
  have he' : Continuous fun v : ℝ => r * Real.exp (-Real.arsinh (Real.sqrt v)) :=
    continuous_const.mul (Real.continuous_exp.comp (Real.continuous_arsinh.comp Real.continuous_sqrt).neg)
  show Continuous fun v : ℝ =>
    !![r * Real.exp (Real.arsinh (Real.sqrt v)), (0 : ℝ); 0, r * Real.exp (-Real.arsinh (Real.sqrt v))]
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    first | exact he | exact he' | exact continuous_const

private theorem exists_forall_le_apply_diagonalElt_eq_zero {f : GL (Fin 2) ℝ → ℂ}
    (hK : ∃ K : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K ∧
      ∀ g : GL (Fin 2) ℝ, f g ≠ 0 → (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K)
    (r : ℝ) (hr : 0 < r) : ∃ V : ℝ, ∀ v : ℝ, V ≤ v → f (diagonalElt r hr v) = 0 := by
  obtain ⟨K, hKc, hKf⟩ := hK
  obtain ⟨B, hB⟩ := (hKc.image (continuous_id.matrix_elem 0 0)).bddAbove
  refine ⟨(max B 0 / r) ^ 2 + 1, fun v hv => ?_⟩
  by_contra hne
  have hv0 : (0 : ℝ) ≤ v := le_trans (by positivity) hv
  have h00 : ((diagonalElt r hr v : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 ≤ B :=
    hB ⟨_, hKf _ hne, rfl⟩
  rw [coe_diagonalElt r hr v hv0] at h00
  simp only [Matrix.of_apply, Matrix.cons_val_zero] at h00
  have h1 : max B 0 / r < Real.sqrt v := by
    rw [Real.lt_sqrt (div_nonneg (le_max_right B 0) hr.le)]
    linarith
  have h2 := (div_lt_iff₀ hr).mp h1
  nlinarith [mul_nonneg hr.le (Real.sqrt_nonneg (1 + v)), le_max_left B 0]

private theorem apply_eq_pow_div_norm_mul_apply_diagonal (m : ℕ) (f : GL (Fin 2) ℝ → ℂ)
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (g : GL (Fin 2) ℝ) (a b : ℂ)
    (ha : a = ⟨((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2,
      ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2⟩)
    (hb : b = ⟨((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2,
      -(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2)⟩)
    (ha0 : a ≠ 0) (d : GL (Fin 2) ℝ) (hd : (d : Matrix (Fin 2) (Fin 2) ℝ) = !![‖a‖ + ‖b‖, 0; 0, ‖a‖ - ‖b‖]) :
    f g = (a / (‖a‖ : ℂ)) ^ m * f d := by
  have hz : Complex.exp ((Complex.arg a : ℂ) * Complex.I) = a / (‖a‖ : ℂ) := by
    rw [eq_div_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha0)), mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I a
  subst ha
  subst hb
  rw [RotationTypeProfile.apply_eq_exp_mul_arg_mul_apply_diagonal_of_weight m f htype g d hd, mul_assoc,
    Complex.exp_nat_mul, hz]

private theorem upperHalfPlaneElt_inv (x y : ℝ) (hy : 0 < y) :
    (upperHalfPlaneElt x y hy)⁻¹ = upperHalfPlaneElt (-x / y) (1 / y) (by positivity) := by
  refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
  show !![y, x; 0, 1] * !![1 / y, -x / y; 0, 1] = (1 : Matrix (Fin 2) (Fin 2) ℝ)
  have hy' : y ≠ 0 := hy.ne'
  have h1 : y * (1 / y) = 1 := by
    field_simp
  have h2 : y * (-x / y) = -x := by
    field_simp
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  simp only [h1, h2, mul_zero, zero_mul, mul_one, add_zero, zero_add, neg_add_cancel]

private theorem norm_profileCoord (r : ℝ) (hr : 0 < r) (θ C v : ℝ) (hv : v = Real.sin θ ^ 2 * (C ^ 2 - 1)) :
    ‖(⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ)‖ = r * Real.sqrt (1 + v) := by
  rw [Complex.norm_def, Complex.normSq_mk]
  conv_rhs => rw [← Real.sqrt_sq hr.le]
  rw [← Real.sqrt_mul (sq_nonneg r)]
  congr 1
  rw [hv]
  linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ

private theorem apply_conj_ellipticElt_eq (m : ℕ) (f : GL (Fin 2) ℝ → ℂ)
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (r : ℝ) (hr : 0 < r) (θ x y : ℝ) (hy : 0 < y) (C : ℝ) (hC : C = (x ^ 2 + y ^ 2 + 1) / (2 * y))
    (v : ℝ) (hv : v = Real.sin θ ^ 2 * (C ^ 2 - 1)) :
    f (upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹) =
      ((⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ) / ((r * Real.sqrt (1 + v) : ℝ) : ℂ)) ^ m *
        f (diagonalElt r hr v) := by
  have hy' : y ≠ 0 := hy.ne'
  have hC1 : 1 ≤ C := by
    rw [hC, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
  have hv0 : 0 ≤ v := by
    rw [hv]
    exact mul_nonneg (sq_nonneg _) (by nlinarith)
  set g : GL (Fin 2) ℝ := upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹ with hg
  have hgval : (g : Matrix (Fin 2) (Fin 2) ℝ) =
      !![y, x; 0, 1] * !![r * Real.cos θ, r * Real.sin θ; -(r * Real.sin θ), r * Real.cos θ] *
        !![1 / y, -x / y; 0, 1] := by
    rw [hg, upperHalfPlaneElt_inv x y hy, Units.val_mul, Units.val_mul]
    rfl
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at hgval
  have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = r * Real.cos θ - x * (r * Real.sin θ) / y := by
    rw [hgval]
    simp only [Matrix.of_apply, Matrix.cons_val_zero]
    field_simp
    ring
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = r * Real.sin θ * (x ^ 2 + y ^ 2) / y := by
    rw [hgval]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = -(r * Real.sin θ) / y := by
    rw [hgval]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = r * Real.cos θ + x * (r * Real.sin θ) / y := by
    rw [hgval]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have hnorm_a := norm_profileCoord r hr θ C v hv
  have ha0 : (⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm_a
    have : 0 < r * Real.sqrt (1 + v) := by positivity
    linarith
  have ha_eq : (⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ) =
      ⟨((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2,
        ((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2⟩ := by
    rw [h00, h01, h10, h11, hC]
    apply Complex.ext <;> (dsimp only; field_simp; ring)
  have hnorm_b : ‖(⟨((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2,
      -(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2)⟩ : ℂ)‖ =
      r * Real.sqrt v := by
    rw [Complex.norm_def, Complex.normSq_mk, h00, h01, h10, h11]
    conv_rhs => rw [← Real.sqrt_sq hr.le]
    rw [← Real.sqrt_mul (sq_nonneg r)]
    congr 1
    rw [hv, hC]
    first | (field_simp; done) | (field_simp; ring)
  have hd_eq : ((diagonalElt r hr v : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![‖(⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ)‖ +
          ‖(⟨((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2,
            -(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2)⟩ : ℂ)‖, 0; 0,
        ‖(⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ)‖ -
          ‖(⟨((g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 - (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) / 2,
            -(((g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 + (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0) / 2)⟩ : ℂ)‖] := by
    rw [coe_diagonalElt r hr v hv0, hnorm_a, hnorm_b, mul_add, mul_sub]
  rw [apply_eq_pow_div_norm_mul_apply_diagonal m f htype g _ _ ha_eq rfl ha0 (diagonalElt r hr v) hd_eq, hnorm_a]

private noncomputable def ellipticProfile (m : ℕ) (f : GL (Fin 2) ℝ → ℂ) (r : ℝ) (hr : 0 < r) (θ : ℝ) (C : ℝ) : ℂ :=
  ((2 * ((((Real.cos θ : ℂ) +
        (Real.sqrt (Real.sin θ ^ 2 + max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0) : ℂ) * Complex.I) ^ m).re /
      Real.sqrt (1 + max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0) ^ m) : ℝ) : ℂ) *
    f (diagonalElt r hr (max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0))

private theorem apply_add_apply_eq_ellipticProfile (m : ℕ) (f : GL (Fin 2) ℝ → ℂ)
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (r : ℝ) (hr : 0 < r) (θ : ℝ) (hθ : 0 ≤ Real.sin θ) (x y : ℝ) (hy : 0 < y) :
    f (upperHalfPlaneElt x y hy * ellipticElt r θ hr * (upperHalfPlaneElt x y hy)⁻¹) +
        f (upperHalfPlaneElt x y hy * ellipticElt r (-θ) hr * (upperHalfPlaneElt x y hy)⁻¹) =
      ellipticProfile m f r hr θ ((x ^ 2 + y ^ 2 + 1) / (2 * y)) := by
  set C : ℝ := (x ^ 2 + y ^ 2 + 1) / (2 * y) with hC
  set v : ℝ := Real.sin θ ^ 2 * (C ^ 2 - 1) with hv
  have hC1 : 1 ≤ C := by
    rw [hC, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg x, sq_nonneg (y - 1)]
  have hv0 : 0 ≤ v := by
    rw [hv]
    exact mul_nonneg (sq_nonneg _) (by nlinarith)
  have hv' : v = Real.sin (-θ) ^ 2 * (C ^ 2 - 1) := hv.trans (by rw [Real.sin_neg, neg_sq])
  rw [apply_conj_ellipticElt_eq m f htype r hr θ x y hy C hC v hv,
    apply_conj_ellipticElt_eq m f htype r hr (-θ) x y hy C hC v hv', ← add_mul]
  unfold ellipticProfile
  rw [← hv, max_eq_left hv0]

  have hconj : (⟨r * Real.cos (-θ), r * Real.sin (-θ) * C⟩ : ℂ) =
      (starRingEnd ℂ) (⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ) := by
    apply Complex.ext
    · simp only [Complex.conj_re, Real.cos_neg]
    · simp only [Complex.conj_im, Real.sin_neg]
      ring
  have hsecond : ((starRingEnd ℂ) (⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ) / ((r * Real.sqrt (1 + v) : ℝ) : ℂ)) ^ m =
      (starRingEnd ℂ) (((⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ) / ((r * Real.sqrt (1 + v) : ℝ) : ℂ)) ^ m) := by
    rw [map_pow, map_div₀, Complex.conj_ofReal]

  have hsC : Real.sqrt (Real.sin θ ^ 2 + v) = Real.sin θ * C := by
    have h : Real.sin θ ^ 2 + v = (Real.sin θ * C) ^ 2 := by rw [hv]; ring
    rw [h, Real.sqrt_sq (mul_nonneg hθ (by linarith))]
  have hquot : (⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ) / ((r * Real.sqrt (1 + v) : ℝ) : ℂ) =
      ((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) / (Real.sqrt (1 + v) : ℂ) := by
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have hnum : (⟨r * Real.cos θ, r * Real.sin θ * C⟩ : ℂ) =
        (r : ℂ) * ((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) := by
      rw [hsC]
      apply Complex.ext <;>
        simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] <;>
        ring
    rw [hnum, Complex.ofReal_mul, mul_div_mul_left _ _ hr']
  rw [hconj, hsecond, Complex.add_conj, hquot, div_pow, ← Complex.ofReal_pow, Complex.div_ofReal_re]

private theorem continuous_ellipticProfile (m : ℕ) (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f) (r : ℝ) (hr : 0 < r)
    (θ : ℝ) : Continuous (ellipticProfile m f r hr θ) := by
  have hvC : Continuous fun C : ℝ => max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0 :=
    (continuous_const.mul ((continuous_id.pow 2).sub continuous_const)).max continuous_const
  have hden : ∀ C : ℝ, Real.sqrt (1 + max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0) ^ m ≠ 0 := fun C =>
    pow_ne_zero _ (Real.sqrt_pos.mpr (by positivity)).ne'
  have hnum : Continuous fun C : ℝ =>
      2 * ((((Real.cos θ : ℂ) +
          (Real.sqrt (Real.sin θ ^ 2 + max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0) : ℂ) * Complex.I) ^ m).re /
        Real.sqrt (1 + max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0) ^ m) := by
    refine continuous_const.mul
      (Continuous.div ?_ ((Real.continuous_sqrt.comp (continuous_const.add hvC)).pow m) hden)
    exact Complex.continuous_re.comp ((continuous_const.add
      ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.add hvC))).mul
        continuous_const)).pow m)
  show Continuous fun C : ℝ =>
    ((2 * ((((Real.cos θ : ℂ) +
          (Real.sqrt (Real.sin θ ^ 2 + max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0) : ℂ) * Complex.I) ^ m).re /
        Real.sqrt (1 + max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0) ^ m) : ℝ) : ℂ) *
      f (diagonalElt r hr (max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0))
  exact (Complex.continuous_ofReal.comp hnum).mul (hf.comp ((continuous_diagonalElt r hr).comp hvC))

private theorem hasCompactSupport_ellipticProfile (m : ℕ) (f : GL (Fin 2) ℝ → ℂ)
    (hK : ∃ K : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K ∧
      ∀ g : GL (Fin 2) ℝ, f g ≠ 0 → (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K)
    (r : ℝ) (hr : 0 < r) (θ : ℝ) (hs : 0 < Real.sin θ) : HasCompactSupport (ellipticProfile m f r hr θ) := by
  obtain ⟨V, hV⟩ := exists_forall_le_apply_diagonalElt_eq_zero hK r hr
  have hs2 : 0 < Real.sin θ ^ 2 := pow_pos hs 2
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Real.sqrt (max V 0 / Real.sin θ ^ 2 + 1) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; exact Real.sqrt_nonneg _
  have hR2 : R ^ 2 = max V 0 / Real.sin θ ^ 2 + 1 := by rw [hR]; exact Real.sq_sqrt (by positivity)
  refine HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-R) R)) fun C hC => ?_
  have hC2 : R ^ 2 < C ^ 2 := by
    rw [Set.mem_Icc, not_and_or] at hC
    rcases hC with h | h
    · have h' := not_le.mp h
      nlinarith
    · have h' := not_le.mp h
      nlinarith
  have hVle : V ≤ max (Real.sin θ ^ 2 * (C ^ 2 - 1)) 0 := by
    refine le_trans (le_max_left V 0) (le_trans ?_ (le_max_left _ _))
    rw [hR2] at hC2
    have h1 : max V 0 / Real.sin θ ^ 2 < C ^ 2 - 1 := by linarith
    rw [div_lt_iff₀ hs2] at h1
    nlinarith
  unfold ellipticProfile
  rw [hV _ hVle, mul_zero]

private theorem ellipticTransform_eq_integral_profile (m : ℕ) (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f)
    (hK : ∃ K : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K ∧
      ∀ g : GL (Fin 2) ℝ, f g ≠ 0 → (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K)
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (r : ℝ) (hr : 0 < r) (θ : ℝ) (hθ : 0 ≤ Real.sin θ) :
    ellipticTransform f r θ =
      8 * (Real.pi : ℂ) * ∫ v in Set.Ioi (0 : ℝ), f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
        (((((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
          Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ) := by
  rcases hθ.lt_or_eq with hs | hs0
  · have hs' : Real.sin θ ≠ 0 := hs.ne'

    have hrad := HyperbolicRadialIntegration.integral_integral_eq (ellipticProfile m f r hr θ)
      (continuous_ellipticProfile m f hf r hr θ) (hasCompactSupport_ellipticProfile m f hK r hr θ hs)

    have himage : (fun v : ℝ => Real.sqrt (Real.sin θ ^ 2 + v) / Real.sin θ) '' Set.Ioi 0 = Set.Ioi 1 := by
      ext c
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hv' : (0 : ℝ) < v := hv
        show 1 < Real.sqrt (Real.sin θ ^ 2 + v) / Real.sin θ
        rw [one_lt_div hs]
        calc Real.sin θ = Real.sqrt (Real.sin θ ^ 2) := (Real.sqrt_sq hs.le).symm
          _ < Real.sqrt (Real.sin θ ^ 2 + v) := Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
      · intro hc
        have hc' : (1 : ℝ) < c := hc
        refine ⟨Real.sin θ ^ 2 * (c ^ 2 - 1), ?_, ?_⟩
        · show (0 : ℝ) < Real.sin θ ^ 2 * (c ^ 2 - 1)
          exact mul_pos (pow_pos hs 2) (by nlinarith)
        · show Real.sqrt (Real.sin θ ^ 2 + Real.sin θ ^ 2 * (c ^ 2 - 1)) / Real.sin θ = c
          have h : Real.sin θ ^ 2 + Real.sin θ ^ 2 * (c ^ 2 - 1) = (Real.sin θ * c) ^ 2 := by ring
          rw [h, Real.sqrt_sq (mul_nonneg hs.le (by linarith))]
          field_simp
    have hderiv : ∀ v ∈ Set.Ioi (0 : ℝ),
        HasDerivWithinAt (fun v : ℝ => Real.sqrt (Real.sin θ ^ 2 + v) / Real.sin θ)
          (1 / (2 * Real.sqrt (Real.sin θ ^ 2 + v)) / Real.sin θ) (Set.Ioi 0) v := by
      intro v hv
      have hv' : (0 : ℝ) < v := hv
      have hne : Real.sin θ ^ 2 + v ≠ 0 := by positivity
      exact ((((hasDerivAt_id v).const_add (Real.sin θ ^ 2)).sqrt hne).div_const (Real.sin θ)).hasDerivWithinAt
    have hinj : Set.InjOn (fun v : ℝ => Real.sqrt (Real.sin θ ^ 2 + v) / Real.sin θ) (Set.Ioi 0) := by
      intro v₁ hv₁ v₂ hv₂ h
      have hv₁' : (0 : ℝ) < v₁ := hv₁
      have hv₂' : (0 : ℝ) < v₂ := hv₂
      have h' : Real.sqrt (Real.sin θ ^ 2 + v₁) = Real.sqrt (Real.sin θ ^ 2 + v₂) := (div_left_inj' hs').mp h
      have h'' := (Real.sqrt_inj (by positivity) (by positivity)).mp h'
      linarith
    have hcov : (∫ c in Set.Ioi (1 : ℝ), ellipticProfile m f r hr θ c) =
        ∫ v in Set.Ioi (0 : ℝ), |1 / (2 * Real.sqrt (Real.sin θ ^ 2 + v)) / Real.sin θ| •
          ellipticProfile m f r hr θ (Real.sqrt (Real.sin θ ^ 2 + v) / Real.sin θ) := by
      rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]

    have hpt : ∀ v ∈ Set.Ioi (0 : ℝ),
        f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
            (((((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
              Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ) =
          (Real.sin θ : ℂ) ^ 2 * (|1 / (2 * Real.sqrt (Real.sin θ ^ 2 + v)) / Real.sin θ| •
            ellipticProfile m f r hr θ (Real.sqrt (Real.sin θ ^ 2 + v) / Real.sin θ)) := by
      intro v hv
      have hv' : (0 : ℝ) < v := hv
      have hsv : 0 < Real.sqrt (Real.sin θ ^ 2 + v) := Real.sqrt_pos.mpr (by positivity)
      have h1v : 0 < Real.sqrt (1 + v) := Real.sqrt_pos.mpr (by positivity)
      have hsvC : (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsv.ne'
      have h1vC : (Real.sqrt (1 + v) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h1v.ne'
      have hsC : (Real.sin θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs'
      have hmax : max (Real.sin θ ^ 2 * ((Real.sqrt (Real.sin θ ^ 2 + v) / Real.sin θ) ^ 2 - 1)) 0 = v := by
        rw [div_pow, Real.sq_sqrt (by positivity)]
        have h : Real.sin θ ^ 2 * ((Real.sin θ ^ 2 + v) / Real.sin θ ^ 2 - 1) = v := by
          first | (field_simp; done) | (field_simp; ring)
        rw [h, max_eq_left hv'.le]
      have habs : |1 / (2 * Real.sqrt (Real.sin θ ^ 2 + v)) / Real.sin θ| =
          1 / (2 * Real.sqrt (Real.sin θ ^ 2 + v)) / Real.sin θ := abs_of_pos (by positivity)
      unfold ellipticProfile
      rw [hmax, habs, Complex.real_smul]
      push_cast
      field_simp
    rw [ellipticTransform, dif_pos hr,
      setIntegral_congr_fun measurableSet_Ioi (g := fun y : ℝ => ∫ x : ℝ,
        ellipticProfile m f r hr θ ((x ^ 2 + y ^ 2 + 1) / (2 * y)) / ((y : ℂ) ^ 2)) _,
      hrad, hcov, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
    · push_cast
      ring
    · intro y hy
      have hy' : (0 : ℝ) < y := hy
      simp only [dif_pos hy', apply_add_apply_eq_ellipticProfile m f htype r hr θ hθ]
  · have h0 : Real.sin θ = 0 := hs0.symm
    simp [ellipticTransform, hr, h0]

private theorem norm_circlePoint (θ v : ℝ) (hv : 0 ≤ v) :
    ‖(Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I‖ = Real.sqrt (1 + v) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  have hre : ((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I).re = Real.cos θ := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him : ((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I).im =
      Real.sqrt (Real.sin θ ^ 2 + v) := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre, him, Real.sq_sqrt (by positivity)]
  congr 1
  linear_combination Real.cos_sq_add_sin_sq θ

private theorem integrable_ellipticModeIntegrand (m : ℕ) (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f)
    (hK : ∃ K : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K ∧
      ∀ g : GL (Fin 2) ℝ, f g ≠ 0 → (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K)
    (r : ℝ) (hr : 0 < r) (k : ℤ) :
    Integrable (fun p : ℝ × ℝ => f (diagonalElt r hr p.2) / ((Real.sqrt (1 + p.2) : ℂ) ^ m) *
        (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos p.1) *
            (((Real.cos p.1 : ℂ) + (Real.sqrt (Real.sin p.1 ^ 2 + p.2) : ℂ) * Complex.I) ^ m).re * Real.sin p.1 /
          Real.sqrt (Real.sin p.1 ^ 2 + p.2) : ℝ) : ℂ))
      (((volume : Measure ℝ).restrict (Set.Ioc 0 Real.pi)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) := by
  obtain ⟨V, hV⟩ := exists_forall_le_apply_diagonalElt_eq_zero hK r hr
  have hcf : ContinuousOn (fun v : ℝ => f (diagonalElt r hr v)) (Set.Icc 0 V) :=
    (hf.comp (continuous_diagonalElt r hr)).continuousOn
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hcf
  have hcU : ContinuousOn (fun θ : ℝ => (Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ)) (Set.Icc 0 Real.pi) :=
    ((Polynomial.continuous (Polynomial.Chebyshev.U ℝ k)).comp Real.continuous_cos).continuousOn
  obtain ⟨MU, hMU⟩ := isCompact_Icc.exists_bound_of_continuousOn hcU
  have hMf0 : (0 : ℝ) ≤ max Mf 0 := le_max_right _ _
  have hMU0 : (0 : ℝ) ≤ max MU 0 := le_max_right _ _
  have hc0 : (0 : ℝ) ≤ max Mf 0 * max MU 0 := mul_nonneg hMf0 hMU0
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hS : MeasurableSet (Set.Ioc (0 : ℝ) Real.pi ×ˢ Set.Ioi (0 : ℝ) : Set (ℝ × ℝ)) :=
    measurableSet_Ioc.prod measurableSet_Ioi
  have hKc : IsCompact (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) V : Set (ℝ × ℝ)) := isCompact_Icc.prod isCompact_Icc
  have hKm : MeasurableSet (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) V : Set (ℝ × ℝ)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hmaj : Integrable
      ((Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) V : Set (ℝ × ℝ)).indicator fun _ : ℝ × ℝ => max Mf 0 * max MU 0)
      ((volume : Measure (ℝ × ℝ)).restrict (Set.Ioc (0 : ℝ) Real.pi ×ˢ Set.Ioi (0 : ℝ))) :=
    ((integrableOn_const hKc.measure_lt_top.ne).integrable_indicator hKm).integrableOn
  refine Integrable.mono' hmaj ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ hS
    have hden₁ : ∀ p ∈ (Set.Ioc (0 : ℝ) Real.pi ×ˢ Set.Ioi (0 : ℝ) : Set (ℝ × ℝ)),
        ((Real.sqrt (1 + p.2) : ℂ) ^ m) ≠ 0 := by
      intro p hp
      have hv : (0 : ℝ) < p.2 := hp.2
      exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne')
    have hden₂ : ∀ p ∈ (Set.Ioc (0 : ℝ) Real.pi ×ˢ Set.Ioi (0 : ℝ) : Set (ℝ × ℝ)),
        Real.sqrt (Real.sin p.1 ^ 2 + p.2) ≠ 0 := by
      intro p hp
      have hv : (0 : ℝ) < p.2 := hp.2
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
    have hW : Continuous fun p : ℝ × ℝ =>
        (Real.cos p.1 : ℂ) + (Real.sqrt (Real.sin p.1 ^ 2 + p.2) : ℂ) * Complex.I :=
      (Complex.continuous_ofReal.comp (Real.continuous_cos.comp continuous_fst)).add
        ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
          (((Real.continuous_sin.comp continuous_fst).pow 2).add continuous_snd))).mul continuous_const)
    have hnum : Continuous fun p : ℝ × ℝ => (Polynomial.Chebyshev.U ℝ k).eval (Real.cos p.1) *
        (((Real.cos p.1 : ℂ) + (Real.sqrt (Real.sin p.1 ^ 2 + p.2) : ℂ) * Complex.I) ^ m).re * Real.sin p.1 :=
      (((Polynomial.continuous (Polynomial.Chebyshev.U ℝ k)).comp (Real.continuous_cos.comp continuous_fst)).mul
        (Complex.continuous_re.comp (hW.pow m))).mul (Real.continuous_sin.comp continuous_fst)
    refine ContinuousOn.mul (ContinuousOn.div ?_ ?_ hden₁) (Complex.continuous_ofReal.comp_continuousOn ?_)
    · exact (hf.comp ((continuous_diagonalElt r hr).comp continuous_snd)).continuousOn
    · exact ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp (continuous_const.add continuous_snd))).pow
        m).continuousOn
    · exact ContinuousOn.div hnum.continuousOn
        (Real.continuous_sqrt.comp (((Real.continuous_sin.comp continuous_fst).pow 2).add continuous_snd)).continuousOn
        hden₂
  · filter_upwards [ae_restrict_mem hS] with p hp
    have hθ : p.1 ∈ Set.Ioc (0 : ℝ) Real.pi := hp.1
    have hv : (0 : ℝ) < p.2 := hp.2
    have hsin0 : 0 ≤ Real.sin p.1 := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le hθ.2
    by_cases hvV : V ≤ p.2
    · rw [hV _ hvV, zero_div, zero_mul, norm_zero, Set.indicator_apply]
      split_ifs
      · exact hc0
      · exact le_rfl
    · have hvV' := not_le.mp hvV
      have hpK : p ∈ (Set.Icc (0 : ℝ) Real.pi ×ˢ Set.Icc (0 : ℝ) V : Set (ℝ × ℝ)) :=
        ⟨⟨hθ.1.le, hθ.2⟩, hv.le, hvV'.le⟩
      rw [Set.indicator_apply, if_pos hpK]

      have hP : 0 < Real.sqrt (1 + p.2) ^ m := pow_pos (Real.sqrt_pos.mpr (by positivity)) m
      have hsq : 0 < Real.sqrt (Real.sin p.1 ^ 2 + p.2) := Real.sqrt_pos.mpr (by positivity)
      have hfb : ‖f (diagonalElt r hr p.2)‖ ≤ max Mf 0 := (hMf p.2 ⟨hv.le, hvV'.le⟩).trans (le_max_left _ _)
      have hUb : |(Polynomial.Chebyshev.U ℝ k).eval (Real.cos p.1)| ≤ max MU 0 := by
        have h := hMU p.1 ⟨hθ.1.le, hθ.2⟩
        rw [Real.norm_eq_abs] at h
        exact h.trans (le_max_left _ _)
      have hreb : |((((Real.cos p.1 : ℂ) + (Real.sqrt (Real.sin p.1 ^ 2 + p.2) : ℂ) * Complex.I) ^ m).re)| ≤
          Real.sqrt (1 + p.2) ^ m := by
        refine (Complex.abs_re_le_norm _).trans ?_
        rw [norm_pow, norm_circlePoint p.1 p.2 hv.le]
      have hsinb : Real.sin p.1 ≤ Real.sqrt (Real.sin p.1 ^ 2 + p.2) := by
        calc Real.sin p.1 = Real.sqrt (Real.sin p.1 ^ 2) := (Real.sqrt_sq hsin0).symm
          _ ≤ Real.sqrt (Real.sin p.1 ^ 2 + p.2) := Real.sqrt_le_sqrt (by linarith)
      have hq : Real.sin p.1 / Real.sqrt (Real.sin p.1 ^ 2 + p.2) ≤ 1 := (div_le_one hsq).mpr hsinb
      have hq0 : 0 ≤ Real.sin p.1 / Real.sqrt (Real.sin p.1 ^ 2 + p.2) := div_nonneg hsin0 hsq.le

      rw [norm_mul, norm_div, Complex.norm_real, norm_pow, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg (1 + p.2)), abs_div, abs_mul, abs_mul, abs_of_nonneg hsin0,
        abs_of_pos hsq]
      have hfirst : ‖f (diagonalElt r hr p.2)‖ / Real.sqrt (1 + p.2) ^ m *
          |((((Real.cos p.1 : ℂ) + (Real.sqrt (Real.sin p.1 ^ 2 + p.2) : ℂ) * Complex.I) ^ m).re)| ≤ max Mf 0 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hP]
        exact mul_le_mul hfb hreb (abs_nonneg _) hMf0
      have hsecond : |(Polynomial.Chebyshev.U ℝ k).eval (Real.cos p.1)| *
          (Real.sin p.1 / Real.sqrt (Real.sin p.1 ^ 2 + p.2)) ≤ max MU 0 := by
        calc |(Polynomial.Chebyshev.U ℝ k).eval (Real.cos p.1)| * (Real.sin p.1 / Real.sqrt (Real.sin p.1 ^ 2 + p.2))
            ≤ max MU 0 * 1 := mul_le_mul hUb hq hq0 hMU0
          _ = max MU 0 := mul_one _
      calc ‖f (diagonalElt r hr p.2)‖ / Real.sqrt (1 + p.2) ^ m *
            (|(Polynomial.Chebyshev.U ℝ k).eval (Real.cos p.1)| *
                |((((Real.cos p.1 : ℂ) + (Real.sqrt (Real.sin p.1 ^ 2 + p.2) : ℂ) * Complex.I) ^ m).re)| *
              Real.sin p.1 / Real.sqrt (Real.sin p.1 ^ 2 + p.2))
          = (‖f (diagonalElt r hr p.2)‖ / Real.sqrt (1 + p.2) ^ m *
              |((((Real.cos p.1 : ℂ) + (Real.sqrt (Real.sin p.1 ^ 2 + p.2) : ℂ) * Complex.I) ^ m).re)|) *
            (|(Polynomial.Chebyshev.U ℝ k).eval (Real.cos p.1)| *
              (Real.sin p.1 / Real.sqrt (Real.sin p.1 ^ 2 + p.2))) := by ring
        _ ≤ max Mf 0 * max MU 0 :=
          mul_le_mul hfirst hsecond (mul_nonneg (abs_nonneg _) hq0) hMf0

private theorem reduction_ellipticConjunct
    (m : ℕ) (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f)
    (hK : ∃ K : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K ∧
      ∀ g : GL (Fin 2) ℝ, f g ≠ 0 → (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K)
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (r : ℝ) (hr : 0 < r) (d : ℝ → GL (Fin 2) ℝ)
    (hd : ∀ v : ℝ, 0 ≤ v → ((d v : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * (Real.sqrt (1 + v) + Real.sqrt v), 0; 0, r * (Real.sqrt (1 + v) - Real.sqrt v)]) :
    (∀ k : ℤ,
      (∫ θ in (0 : ℝ)..Real.pi,
          ellipticTransform f r θ * (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) : ℝ) : ℂ)) =
        8 * (Real.pi : ℂ) *
          ∫ v in Set.Ioi (0 : ℝ), f (d v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
            ((∫ θ in (0 : ℝ)..Real.pi,
                (Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) *
                    (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
                  Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ)) := by
  intro k

  have hdd : ∀ v : ℝ, 0 ≤ v → f (d v) = f (diagonalElt r hr v) := fun v hv =>
    congrArg f (Units.ext (by rw [hd v hv, coe_diagonalElt r hr v hv]))

  have hright : ∀ v ∈ Set.Ioi (0 : ℝ),
      f (d v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
          ((∫ θ in (0 : ℝ)..Real.pi, (Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) *
              (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
            Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ) =
        ∫ θ in (0 : ℝ)..Real.pi, f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
          (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) *
              (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
            Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ) := by
    intro v hv
    rw [hdd v (Set.mem_Ioi.mp hv).le, ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]

  have hleft : ∀ θ ∈ Set.uIcc (0 : ℝ) Real.pi,
      ellipticTransform f r θ * (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) : ℝ) : ℂ) =
        8 * (Real.pi : ℂ) * ∫ v in Set.Ioi (0 : ℝ), f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
          (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) *
              (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
            Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ) := by
    intro θ hθ
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    have hθ' : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have hpt : ∀ v : ℝ,
        f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
              (((((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
                Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ) *
            (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) : ℝ) : ℂ) =
          f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
            (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) *
                (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
              Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ) := by
      intro v
      push_cast
      ring
    rw [ellipticTransform_eq_integral_profile m f hf hK htype r hr θ hθ', mul_assoc, ← integral_mul_const]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioi fun v _ => hpt v

  have hint : Integrable (Function.uncurry fun θ v : ℝ =>
      f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
        (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) *
            (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
          Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ))
      (((volume : Measure ℝ).restrict (Set.Ioc 0 Real.pi)).prod ((volume : Measure ℝ).restrict (Set.Ioi 0))) :=
    integrable_ellipticModeIntegrand m f hf hK r hr k
  have hswap : (∫ θ in (0 : ℝ)..Real.pi, ∫ v in Set.Ioi (0 : ℝ),
        f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
          (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) *
              (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
            Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ)) =
      ∫ v in Set.Ioi (0 : ℝ), ∫ θ in (0 : ℝ)..Real.pi,
        f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
          (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) *
              (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
            Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ) := by
    simp_rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    exact integral_integral_swap hint
  rw [intervalIntegral.integral_congr hleft, intervalIntegral.integral_const_mul, hswap,
    setIntegral_congr_fun measurableSet_Ioi hright]

end EllipticSide
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

private theorem integral_kernel_mul_bracket_eq {m : ℕ} {f : GL (Fin 2) ℝ → ℂ}
    (hneg : ∀ g, f (-g) = (-1) ^ m * f g) (κ : ℝ → ℝ) (ε : ℂ) (r : ℝ) :
    (∫ t : ℝ, ((κ |t| : ℝ) : ℂ) *
        (splitTransform f (r * Real.exp t) (r * Real.exp (-t)) +
          ε * splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t))))) =
      (1 + ε * (-1 : ℂ) ^ m) *
        ∫ t : ℝ, ((κ |t| : ℝ) : ℂ) * splitTransform f (r * Real.exp t) (r * Real.exp (-t)) := by
  rw [← integral_const_mul]
  congr 1
  funext t
  rw [splitTransform_neg_neg hneg]
  ring

private theorem rotation_mem_rowIsometrySubgroup₀ (θ : ℝ) : rotation θ ∈ rowIsometrySubgroup₀ ℝ := by
  have hval : (rotation θ : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := rfl
  have hdet : (rotation θ : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [hval, Matrix.det_fin_two_of]
    linear_combination Real.cos_sq_add_sin_sq (x := θ)
  rw [mem_rowIsometrySubgroup₀_iff]
  refine ⟨hdet, ?_⟩
  constructor
  · rw [hdet, norm_one]
  · intro x y
    rw [hval]
    show ‖x * Real.cos θ + y * -Real.sin θ‖ ^ 2 + ‖x * Real.sin θ + y * Real.cos θ‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2
    simp only [Real.norm_eq_abs, sq_abs]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq (x := θ)

private theorem splitTransform_eq_integral_upperTriangular {m : ℕ} {f : GL (Fin 2) ℝ → ℂ}
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (a₁ a₂ : ℝ) (h : a₁ * a₂ ≠ 0) :
    splitTransform f a₁ a₂ = ∫ u : ℝ, f (upperTriangular a₁ a₂ u h) := by
  have hinv : ∀ θ u : ℝ,
      f (rotation θ * upperTriangular a₁ a₂ u h * (rotation θ)⁻¹) = f (upperTriangular a₁ a₂ u h) := by
    intro θ u
    have key := htype ⟨rotation θ, rotation_mem_rowIsometrySubgroup₀ θ⟩
      (⟨rotation θ, rotation_mem_rowIsometrySubgroup₀ θ⟩⁻¹) (upperTriangular a₁ a₂ u h)
    rw [Subgroup.coe_inv, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_mul] at key
    exact key
  unfold splitTransform
  rw [dif_pos h]
  simp_rw [hinv]
  rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  push_cast
  rw [one_div, inv_mul_cancel_left₀ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]

private theorem apply_upperTriangular_exp_eq {m : ℕ} {f : GL (Fin 2) ℝ → ℂ}
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (r : ℝ) (hr : 0 < r) (d : ℝ → GL (Fin 2) ℝ)
    (hd : ∀ v : ℝ, 0 ≤ v → ((d v : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * (Real.sqrt (1 + v) + Real.sqrt v), 0; 0, r * (Real.sqrt (1 + v) - Real.sqrt v)])
    (t u : ℝ) (h : r * Real.exp t * (r * Real.exp (-t)) ≠ 0) :
    f (upperTriangular (r * Real.exp t) (r * Real.exp (-t)) u h) =
      (((Real.cosh t : ℂ) + ((u / (2 * r) : ℝ) : ℂ) * Complex.I) /
            (Real.sqrt (1 + (Real.sinh t ^ 2 + (u / (2 * r)) ^ 2)) : ℂ)) ^ m *
        f (d (Real.sinh t ^ 2 + (u / (2 * r)) ^ 2)) := by
  set v : ℝ := Real.sinh t ^ 2 + (u / (2 * r)) ^ 2 with hv
  have hv0 : 0 ≤ v := by positivity
  have hu : r * (u / (2 * r)) = u / 2 := by
    rw [← mul_div_assoc, mul_comm r u, mul_div_mul_right _ _ hr.ne']
  have hT : ((upperTriangular (r * Real.exp t) (r * Real.exp (-t)) u h : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![r * Real.exp t, u; 0, r * Real.exp (-t)] := rfl
  have hna : ‖(⟨r * Real.cosh t, u / 2⟩ : ℂ)‖ = r * Real.sqrt (1 + v) := by
    rw [show r * Real.sqrt (1 + v) = Real.sqrt (r ^ 2 * (1 + v)) by
      rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le], Complex.norm_def, Complex.normSq_mk]
    congr 1
    rw [← hu, hv]
    linear_combination r ^ 2 * Real.cosh_sq' (x := t)
  have hnb : ‖(⟨r * Real.sinh t, -(u / 2)⟩ : ℂ)‖ = r * Real.sqrt v := by
    rw [show r * Real.sqrt v = Real.sqrt (r ^ 2 * v) by
      rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le], Complex.norm_def, Complex.normSq_mk]
    congr 1
    rw [← hu, hv]
    ring
  have hquot : (⟨r * Real.cosh t, u / 2⟩ : ℂ) / ((r * Real.sqrt (1 + v) : ℝ) : ℂ) =
      ((Real.cosh t : ℂ) + ((u / (2 * r) : ℝ) : ℂ) * Complex.I) / (Real.sqrt (1 + v) : ℂ) := by
    have hnum : (⟨r * Real.cosh t, u / 2⟩ : ℂ) =
        (r : ℂ) * ((Real.cosh t : ℂ) + ((u / (2 * r) : ℝ) : ℂ) * Complex.I) := by
      apply Complex.ext
      · simp only [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one]
      · simp only [Complex.mul_re, Complex.add_re, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one, zero_add]
        exact hu.symm
    rw [hnum, Complex.ofReal_mul, mul_div_mul_left _ _ (Complex.ofReal_ne_zero.mpr hr.ne')]
  rw [apply_eq_pow_div_norm_mul_apply_diagonal m f htype _ ⟨r * Real.cosh t, u / 2⟩
    ⟨r * Real.sinh t, -(u / 2)⟩ ?_ ?_ ?_ (d v) ?_, hna, hquot]
  · rw [hT]
    apply Complex.ext <;> simp [Real.cosh_eq] <;> ring
  · rw [hT]
    apply Complex.ext <;> simp [Real.sinh_eq] <;> ring
  · intro h0
    have h0' := congrArg Complex.re h0
    change r * Real.cosh t = 0 at h0'
    exact (mul_pos hr (Real.cosh_pos t)).ne' h0'
  · rw [hna, hnb, hd v hv0, mul_add, mul_sub]

private theorem reduction_splitConjunct
    (m : ℕ) (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f)
    (hK : ∃ K : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K ∧
      ∀ g : GL (Fin 2) ℝ, f g ≠ 0 → (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K)
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (r : ℝ) (hr : 0 < r) (d : ℝ → GL (Fin 2) ℝ)
    (hd : ∀ v : ℝ, 0 ≤ v → ((d v : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * (Real.sqrt (1 + v) + Real.sqrt v), 0; 0, r * (Real.sqrt (1 + v) - Real.sqrt v)]) :
    (∀ κ : ℝ → ℝ, Continuous κ → ∀ ε : ℂ,
      (∫ t : ℝ, ((κ |t| : ℝ) : ℂ) *
          (splitTransform f (r * Real.exp t) (r * Real.exp (-t)) +
            ε * splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t))))) =
        2 * (r : ℂ) * (1 + ε * (-1 : ℂ) ^ m) *
          ∫ v in Set.Ioi (0 : ℝ), f (d v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
            ((∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
                κ (Real.arsinh (Real.sqrt v * Real.cos ψ)) *
                    (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                        ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
                  Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℝ) : ℂ)) := by
  intro κ hκ ε
  have hneg := apply_neg_eq_neg_one_pow_mul htype
  have hr2 : ∀ t : ℝ, r * Real.exp t * (r * Real.exp (-t)) ≠ 0 := fun t => by positivity
  have hdd : ∀ v : ℝ, 0 ≤ v → d v = diagonalElt r hr v := fun v hv =>
    Units.ext ((hd v hv).trans (coe_diagonalElt r hr v hv).symm)
  have hF : ContinuousOn (fun v => f (d v)) (Set.Ici 0) :=
    (hf.comp (continuous_diagonalElt r hr)).continuousOn.congr fun v hv => by
      show f (d v) = f (diagonalElt r hr v)
      rw [hdd v (Set.mem_Ici.mp hv)]
  have hFs : ∃ V : ℝ, ∀ v, V ≤ v → f (d v) = 0 := by
    obtain ⟨V, hV⟩ := exists_forall_le_apply_diagonalElt_eq_zero hK r hr
    refine ⟨max V 0, fun v hv => ?_⟩
    rw [hdd v ((le_max_right V 0).trans hv)]
    exact hV v ((le_max_left V 0).trans hv)
  rw [integral_kernel_mul_bracket_eq hneg κ ε r]
  have hH : (∫ t : ℝ, ((κ |t| : ℝ) : ℂ) * splitTransform f (r * Real.exp t) (r * Real.exp (-t))) =
      ∫ t : ℝ, ((κ |t| : ℝ) : ℂ) *
        ∫ u : ℝ, (((Real.cosh t : ℂ) + ((u / (2 * r) : ℝ) : ℂ) * Complex.I) /
              (Real.sqrt (1 + (Real.sinh t ^ 2 + (u / (2 * r)) ^ 2)) : ℂ)) ^ m *
          f (d (Real.sinh t ^ 2 + (u / (2 * r)) ^ 2)) := by
    congr 1
    funext t
    rw [splitTransform_eq_integral_upperTriangular htype _ _ (hr2 t)]
    congr 1
    congr 1
    funext u
    exact apply_upperTriangular_exp_eq htype r hr d hd t u (hr2 t)
  rw [hH, integral_kernel_mul_integral_profile_eq m hr hκ hF hFs]
  ring

end AutomorphicForm.GL2Real
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

p2m_open_scoped "AutomorphicForm AutomorphicForm.GL2Real" in
private theorem
    AutomorphicForm.GL2Real.integral_mul_splitTransform_and_intervalIntegral_ellipticTransform_mul_chebyshevU_eq
    (m : ℕ) (f : GL (Fin 2) ℝ → ℂ) (hf : Continuous f)
    (hK : ∃ K : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K ∧
      ∀ g : GL (Fin 2) ℝ, f g ≠ 0 → (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K)
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    (r : ℝ) (hr : 0 < r) (d : ℝ → GL (Fin 2) ℝ)
    (hd : ∀ v : ℝ, 0 ≤ v → ((d v : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![r * (Real.sqrt (1 + v) + Real.sqrt v), 0; 0, r * (Real.sqrt (1 + v) - Real.sqrt v)]) :
    (∀ κ : ℝ → ℝ, Continuous κ → ∀ ε : ℂ,
      (∫ t : ℝ, ((κ |t| : ℝ) : ℂ) *
          (splitTransform f (r * Real.exp t) (r * Real.exp (-t)) +
            ε * splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t))))) =
        2 * (r : ℂ) * (1 + ε * (-1 : ℂ) ^ m) *
          ∫ v in Set.Ioi (0 : ℝ), f (d v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
            ((∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
                κ (Real.arsinh (Real.sqrt v * Real.cos ψ)) *
                    (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                        ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
                  Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℝ) : ℂ)) ∧
    (∀ k : ℤ,
      (∫ θ in (0 : ℝ)..Real.pi,
          ellipticTransform f r θ * (((Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) : ℝ) : ℂ)) =
        8 * (Real.pi : ℂ) *
          ∫ v in Set.Ioi (0 : ℝ), f (d v) / ((Real.sqrt (1 + v) : ℂ) ^ m) *
            ((∫ θ in (0 : ℝ)..Real.pi,
                (Polynomial.Chebyshev.U ℝ k).eval (Real.cos θ) *
                    (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
                  Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ)) :=
  ⟨AutomorphicForm.GL2Real.reduction_splitConjunct m f hf hK htype r hr d hd,
    AutomorphicForm.GL2Real.reduction_ellipticConjunct m f hf hK htype r hr d hd⟩

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff weyl_mem_rowIsometrySubgroup₀ firstRowℂ archWeightOneℝ archWeightCharℝ archWeightOneℝ_weyl"
namespace GL2Real
p2m_export "AutomorphicForm.GL2Real" "rotation upperTriangular upperHalfPlaneElt ellipticElt splitTransform ellipticTransform discreteSeriesPairing"
p2m_open "AutomorphicForm.GL2Real AutomorphicForm"

open MeasureTheory

private theorem continuous_kernelModeIntegrand (κ : ℝ → ℝ) (hκ : Continuous κ) (v : ℝ) (m : ℕ) :
    Continuous fun ψ : ℝ =>
      κ (Real.arsinh (Real.sqrt v * Real.cos ψ)) *
          (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
              ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
        Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) := by
  have ht : Continuous fun ψ : ℝ => Real.arsinh (Real.sqrt v * Real.cos ψ) :=
    Real.continuous_arsinh.comp (continuous_const.mul Real.continuous_cos)
  refine Continuous.div₀ ((hκ.comp ht).mul (Complex.continuous_re.comp (Continuous.pow ?_ m)))
    (Real.continuous_cosh.comp ht) (fun ψ => (Real.cosh_pos _).ne')
  exact (Complex.continuous_ofReal.comp (Real.continuous_cosh.comp ht)).add
    ((Complex.continuous_ofReal.comp (continuous_const.mul Real.continuous_sin)).mul continuous_const)

private theorem neg_one_pow_mul_neg_one_pow_of_two_dvd {j m : ℕ} (h : 2 ∣ j + m) :
    (-1 : ℂ) ^ j * (-1 : ℂ) ^ m = 1 := by
  rw [← pow_add]
  exact (even_iff_two_dvd.mpr h).neg_one_pow

private theorem hyperbolicMode_exp_eq_chebyshevMode {j m : ℕ} (hj : 2 ≤ j) (hmj : m + 2 ≤ j) (heven : 2 ∣ j + m)
    (v : ℝ) (hv : 0 < v) :
    (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
      Real.exp (-(((j : ℝ) - 1) * Real.arsinh (Real.sqrt v * Real.cos ψ))) *
          (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
              ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
        Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ))) =
      ∫ θ in (0 : ℝ)..Real.pi,
        (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) *
            (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
          Real.sqrt (Real.sin θ ^ 2 + v) := by
  have hK := (chebyshevMode_add_sinhMode_of_two_dvd (j - 2) m (by omega) v hv).2 (by omega)
  have hc1 : ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 := by omega
  have hc2 : ((j - 2 : ℕ) : ℝ) + 1 = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj]; push_cast; ring
  rw [hc1, hc2] at hK
  have hCi : IntervalIntegrable (fun ψ : ℝ =>
          Real.cosh (((j : ℝ) - 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
            (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
          Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ))) volume (-(Real.pi / 2)) (Real.pi / 2) :=
    (continuous_kernelModeIntegrand (fun x => Real.cosh (((j : ℝ) - 1) * x))
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id)) v m).intervalIntegrable _ _
  have hSi : IntervalIntegrable (fun ψ : ℝ =>
          Real.sinh (((j : ℝ) - 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
            (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
          Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ))) volume (-(Real.pi / 2)) (Real.pi / 2) :=
    (continuous_kernelModeIntegrand (fun x => Real.sinh (((j : ℝ) - 1) * x))
      (Real.continuous_sinh.comp (continuous_const.mul continuous_id)) v m).intervalIntegrable _ _
  have hsplit :
      (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
        Real.exp (-(((j : ℝ) - 1) * Real.arsinh (Real.sqrt v * Real.cos ψ))) *
            (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
          Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ))) =
        (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
          Real.cosh (((j : ℝ) - 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
              (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                  ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
            Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ))) -
          (∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
            Real.sinh (((j : ℝ) - 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
                (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                    ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
              Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ))) := by
    rw [← intervalIntegral.integral_sub hCi hSi]
    refine intervalIntegral.integral_congr fun ψ _ => ?_
    simp only [← Real.cosh_sub_sinh]
    ring
  linear_combination hsplit - hK

private theorem chebyshevMode_eq_neg_sinhMode {j m : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m + 1) (heven : 2 ∣ j + m) (v : ℝ)
    (hv : 0 < v) :
    (∫ θ in (0 : ℝ)..Real.pi,
      (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) *
          (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
        Real.sqrt (Real.sin θ ^ 2 + v)) =
      -(∫ ψ in (-(Real.pi / 2))..(Real.pi / 2),
        Real.sinh (((j : ℝ) - 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
            (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
          Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ))) := by
  have hK := (chebyshevMode_add_sinhMode_of_two_dvd (j - 2) m (by omega) v hv).1 (by omega)
  have hc1 : ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 := by omega
  have hc2 : ((j - 2 : ℕ) : ℝ) + 1 = (j : ℝ) - 1 := by
    rw [Nat.cast_sub hj]; push_cast; ring
  rw [hc1, hc2] at hK
  linear_combination hK

private theorem setIntegral_mul_hyperbolicMode_exp_eq {j m : ℕ} (hj : 2 ≤ j) (hmj : m + 2 ≤ j) (heven : 2 ∣ j + m)
    (F : ℝ → ℂ) :
    (∫ v in Set.Ioi (0 : ℝ), F v *
        ((∫ ψ in -(Real.pi / 2)..(Real.pi / 2),
          Real.exp (-(((j : ℝ) - 1) * Real.arsinh (Real.sqrt v * Real.cos ψ))) *
              (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                  ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
            Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℝ) : ℂ)) =
      ∫ v in Set.Ioi (0 : ℝ), F v *
        ((∫ θ in (0 : ℝ)..Real.pi,
          (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) *
              (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
            Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ) :=
  setIntegral_congr_fun measurableSet_Ioi fun v hv => by
    rw [hyperbolicMode_exp_eq_chebyshevMode hj hmj heven v (Set.mem_Ioi.mp hv)]

private theorem setIntegral_mul_chebyshevMode_eq_neg {j m : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m + 1) (heven : 2 ∣ j + m)
    (F : ℝ → ℂ) :
    (∫ v in Set.Ioi (0 : ℝ), F v *
        ((∫ θ in (0 : ℝ)..Real.pi,
          (Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) *
              (((Real.cos θ : ℂ) + (Real.sqrt (Real.sin θ ^ 2 + v) : ℂ) * Complex.I) ^ m).re * Real.sin θ /
            Real.sqrt (Real.sin θ ^ 2 + v) : ℝ) : ℂ)) =
      -∫ v in Set.Ioi (0 : ℝ), F v *
        ((∫ ψ in -(Real.pi / 2)..(Real.pi / 2),
          Real.sinh (((j : ℝ) - 1) * Real.arsinh (Real.sqrt v * Real.cos ψ)) *
              (((Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℂ) +
                  ((Real.sqrt v * Real.sin ψ : ℝ) : ℂ) * Complex.I) ^ m).re /
            Real.cosh (Real.arsinh (Real.sqrt v * Real.cos ψ)) : ℝ) : ℂ) := by
  rw [← MeasureTheory.integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  rw [chebyshevMode_eq_neg_sinhMode hj hjm heven v (Set.mem_Ioi.mp hv), Complex.ofReal_neg, mul_neg]

private theorem eight_mul_sub_eq_zero (r A : ℂ) (hr : r ≠ 0) :
    8 * (Real.pi : ℂ) * A - 2 * (Real.pi : ℂ) / r * (2 * r * (1 + 1) * A) = 0 := by
  have h : 2 * (Real.pi : ℂ) / r * (2 * r * (1 + 1) * A) = 8 * (Real.pi : ℂ) * A * (r / r) := by ring
  rw [h, div_self hr, mul_one, sub_self]

private theorem eight_mul_neg_eq (r S : ℂ) (hr : r ≠ 0) :
    8 * (Real.pi : ℂ) * -S = -((2 * Real.pi : ℝ) : ℂ) * (1 / r) * (2 * r * (1 + 1) * S) := by
  have h : -((2 * Real.pi : ℝ) : ℂ) * (1 / r) * (2 * r * (1 + 1) * S) = 8 * (Real.pi : ℂ) * -S * (r / r) := by
    push_cast; ring
  rw [h, div_self hr, mul_one]

private theorem discreteSeriesPairing_eq_zero_of_le_of_two_dvd {m : ℕ} {f : GL (Fin 2) ℝ → ℂ} (hf : Continuous f)
    (hK : ∃ K : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K ∧
      ∀ g : GL (Fin 2) ℝ, f g ≠ 0 → (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K)
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    {j : ℕ} (hmj : m + 2 ≤ j) (heven : 2 ∣ j + m) (r : ℝ) (hr : 0 < r) :
    discreteSeriesPairing j (splitTransform f) (ellipticTransform f) r = 0 := by
  have hj : 2 ≤ j := le_trans (Nat.le_add_left 2 m) hmj
  obtain ⟨hH, hE⟩ :=
    integral_mul_splitTransform_and_intervalIntegral_ellipticTransform_mul_chebyshevU_eq m f hf hK htype r hr
      (diagonalElt r hr) (coe_diagonalElt r hr)
  have hH1 := hH (fun x => Real.exp (-(((j : ℝ) - 1) * x)))
    (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)) ((-1 : ℂ) ^ j)
  unfold discreteSeriesPairing
  rw [hE ((j : ℤ) - 2), hH1,
    setIntegral_mul_hyperbolicMode_exp_eq hj hmj heven
      (fun v => f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m)),
    neg_one_pow_mul_neg_one_pow_of_two_dvd heven]
  exact eight_mul_sub_eq_zero _ _ (Complex.ofReal_ne_zero.mpr hr.ne')

private theorem intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_two_dvd {m : ℕ} {f : GL (Fin 2) ℝ → ℂ}
    (hf : Continuous f)
    (hK : ∃ K : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K ∧
      ∀ g : GL (Fin 2) ℝ, f g ≠ 0 → (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K)
    (htype : ∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
      f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
        ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g)
    {j : ℕ} (hj : 2 ≤ j) (hjm : j ≤ m + 1) (heven : 2 ∣ j + m) (r : ℝ) (hr : 0 < r) :
    (∫ θ in (0 : ℝ)..Real.pi,
        ellipticTransform f r θ * (((Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
      -((2 * Real.pi : ℝ) : ℂ) * (1 / r : ℂ) *
        ∫ t : ℝ, (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) *
          (splitTransform f (r * Real.exp t) (r * Real.exp (-t)) +
            (-1 : ℂ) ^ j * splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t)))) := by
  obtain ⟨hH, hE⟩ :=
    integral_mul_splitTransform_and_intervalIntegral_ellipticTransform_mul_chebyshevU_eq m f hf hK htype r hr
      (diagonalElt r hr) (coe_diagonalElt r hr)
  have hH1 := hH (fun x => Real.sinh (((j : ℝ) - 1) * x))
    (Real.continuous_sinh.comp (continuous_const.mul continuous_id)) ((-1 : ℂ) ^ j)
  rw [hE ((j : ℤ) - 2), hH1,
    setIntegral_mul_chebyshevMode_eq_neg hj hjm heven
      (fun v => f (diagonalElt r hr v) / ((Real.sqrt (1 + v) : ℂ) ^ m)),
    neg_one_pow_mul_neg_one_pow_of_two_dvd heven]
  exact eight_mul_neg_eq _ _ (Complex.ofReal_ne_zero.mpr hr.ne')

end AutomorphicForm.GL2Real
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

theorem solution :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (m : ℕ) (f : GL (Fin 2) ℝ → ℂ), Continuous f → HasCompactSupport f →
      (∀ (k₁ k₂ : rowIsometrySubgroup₀ ℝ) (g : GL (Fin 2) ℝ),
        f ((k₁ : GL (Fin 2) ℝ) * g * (k₂ : GL (Fin 2) ℝ)) =
          ((archWeightCharℝ (m : ℤ) k₁ : ℂˣ) : ℂ) * ((archWeightCharℝ (m : ℤ) k₂ : ℂˣ) : ℂ) * f g) →
      ∀ j : ℕ, 2 ≤ j → j ≤ m + 1 → ∀ r : ℝ, 0 < r →
        (∫ θ in (0 : ℝ)..Real.pi,
            ellipticTransform f r θ * (((Polynomial.Chebyshev.U ℝ ((j : ℤ) - 2)).eval (Real.cos θ) : ℝ) : ℂ)) =
          -(κ : ℂ) * (1 / r : ℂ) *
            ∫ t : ℝ, (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ) *
              (splitTransform f (r * Real.exp t) (r * Real.exp (-t)) +
                (-1 : ℂ) ^ j * splitTransform f (-(r * Real.exp t)) (-(r * Real.exp (-t)))) := by
  refine ⟨2 * Real.pi, by positivity, ?_⟩
  intro m f hf hfc htype j hj hjm r hr
  have hK : ∃ K : Set (Matrix (Fin 2) (Fin 2) ℝ), IsCompact K ∧
      ∀ g : GL (Fin 2) ℝ, f g ≠ 0 → (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ K :=
    ⟨((↑) : GL (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) '' tsupport f, hfc.isCompact.image Units.continuous_val,
      fun g hg => ⟨g, subset_tsupport f hg, rfl⟩⟩
  by_cases hpar : 2 ∣ j + m
  · exact intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_two_dvd hf hK htype hj hjm hpar r hr
  · have hneg := apply_neg_eq_neg_one_pow_mul htype
    rw [intervalIntegral_ellipticTransform_mul_chebyshevU_eq_zero_of_not_two_dvd hneg hj hpar r,
      integral_mul_splitTransform_bracket_eq_zero_of_not_two_dvd hneg hpar
        (fun t => (Real.sinh (((j : ℝ) - 1) * |t|) : ℂ)) r, mul_zero]

#print axioms solution

end
p2m_reactivate "P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight.FLT.BandStripFubini"

end S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight
end P2MW
export P2MW.S_AutomorphicForm_GL2Real_exists_intervalIntegral_ellipticTransform_mul_chebyshevU_eq_of_le_weight (solution)
