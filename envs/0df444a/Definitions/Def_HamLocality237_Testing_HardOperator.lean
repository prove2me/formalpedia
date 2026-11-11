-- Prove2me | Definitions.Def_HamLocality237_Testing_HardOperator
-- name    : HamLocality237_Testing_HardOperator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:31.418289+00:00
-- url     : https://prove2.me/theorems/6515a4d0-1440-4937-a0a6-5ba7aa735cd5
-- title:
--   The interval bump and bounded coordinate multiplication
-- statement:
--   Let $\mu$ be Lebesgue measure restricted to $[-1/2,1/2]$ and let $\mathcal B=L^2(\mu;\mathbb C)$. Define
--
--   $$\widetilde b(\omega)=\operatorname{expNegInvGlue}(1-16\omega^2),\qquad b=\|\widetilde b\|_{L^2}^{-1}\widetilde b.$$
--
--   Thus the raw bump is $\exp(-1/(1-16\omega^2))$ for $|\omega|<1/4$, and zero otherwise. The file proves that it lies in $L^2$. To construct bounded multiplication, use the globally bounded coordinate representative $m(\omega)=\max\{-1/2,\min\{1/2,\omega\}\}$, which equals $\omega$ on the interval. Define
--
--   $$(Mr)(\omega)=m(\omega)r(\omega),\qquad \|Mr\|_{L^2}\le\tfrac12\|r\|_{L^2}.$$
--
--   The multiplication operator has a real continuous-linear-map body, with the action and norm estimate proved. This is the bump and multiplication part of the hard-ensemble definitions. The Adversary definition constructs the actual block operator and spectral measure from these objects. Unit normalization and self-adjointness are conclusions of the Definition 3.1 and Lemma 3.2 item; no hypothesis postulates them. The total inverse at a zero raw vector is zero, but the source bump is positive on an interval about zero and hence is nonzero in L².The Adversary definition constructs the actual block operator and spectral measure from these objects. Unit normalization and self-adjointness are conclusions of the Definition 3.1 and Lemma 3.2 item; no hypothesis postulates them. The total inverse at a zero raw vector is zero, but the source bump is positive on an interval about zero and hence is nonzero in L².
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), §3.1, Eqs. (7)–(8), p.13 (bump and multiplication part only). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Mathlib

open MeasureTheory
open scoped ENNReal ComplexConjugate
noncomputable section

namespace HamLocality237.Testing

/-- Lebesgue measure on the interval in Eq. (7), p.13. -/
def intervalMeasure : Measure ℝ := volume.restrict (Set.Icc (-1 / 2 : ℝ) (1 / 2))

instance : IsFiniteMeasure intervalMeasure := by
  unfold intervalMeasure
  infer_instance

abbrev BandSpace := Lp ℂ 2 intervalMeasure

def bumpRaw (w : ℝ) : ℂ := (expNegInvGlue (1 - 16 * w ^ 2) : ℝ)

theorem bumpRaw_memLp : MemLp bumpRaw 2 intervalMeasure := by
  have hc : Continuous bumpRaw := by
    unfold bumpRaw
    exact Complex.continuous_ofReal.comp ((@expNegInvGlue.contDiff 0).continuous.comp
      (continuous_const.sub (continuous_const.mul (continuous_id.pow 2))))
  apply MemLp.of_bound hc.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro w
  rw [bumpRaw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (expNegInvGlue.nonneg _)]
  by_cases h : 1 - 16 * w ^ 2 ≤ 0
  · simp [expNegInvGlue, h]
  · rw [expNegInvGlue, if_neg h]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge h)))

def bumpVectorRaw : BandSpace := bumpRaw_memLp.toLp bumpRaw

/-- Eq. (7), p.13, normalization of the smooth bump in L². -/
def bumpVector : BandSpace := (‖bumpVectorRaw‖⁻¹ : ℂ) • bumpVectorRaw

/-- A bounded representative equal to the coordinate on the measure's support. -/
def coordinate (w : ℝ) : ℂ := (max (-1 / 2 : ℝ) (min (1 / 2) w) : ℝ)

theorem coordinate_memLp : MemLp coordinate ∞ intervalMeasure := by
  apply memLp_top_of_bound
    ((Complex.continuous_ofReal.comp
      (continuous_const.max (continuous_const.min continuous_id))).aestronglyMeasurable) (1 / 2)
  apply Filter.Eventually.of_forall
  intro w
  change ‖coordinate w‖ ≤ _
  rw [coordinate, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [le_max_left (-1 / 2 : ℝ) (min (1 / 2) w)]
  · exact max_le (by norm_num) (min_le_left _ _)

def multiplyCoordinate (r : BandSpace) : BandSpace :=
  ((Lp.memLp r).mul coordinate_memLp).toLp (fun w => coordinate w * r w)

theorem multiplyCoordinate_ae (r : BandSpace) :
    multiplyCoordinate r =ᵐ[intervalMeasure] fun w => coordinate w * r w :=
  (Lp.memLp r |>.mul coordinate_memLp).coeFn_toLp

def coordinateLinear : BandSpace →ₗ[ℂ] BandSpace where
  toFun := multiplyCoordinate
  map_add' r s := by
    apply Lp.ext
    filter_upwards [multiplyCoordinate_ae (r + s), multiplyCoordinate_ae r,
      multiplyCoordinate_ae s, Lp.coeFn_add r s,
      Lp.coeFn_add (multiplyCoordinate r) (multiplyCoordinate s)] with w h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1, h5, h4, h2, h3]
    ring
  map_smul' c r := by
    apply Lp.ext
    filter_upwards [multiplyCoordinate_ae (c • r), multiplyCoordinate_ae r,
      Lp.coeFn_smul c r, Lp.coeFn_smul c (multiplyCoordinate r)] with w h1 h2 h3 h4
    change multiplyCoordinate (c • r) w = (c • multiplyCoordinate r) w
    simp only [Pi.smul_apply] at h3 h4
    rw [h1, h4, h3, h2]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

theorem coordinateLinear_bound (r : BandSpace) : ‖coordinateLinear r‖ ≤ (1 / 2 : ℝ) * ‖r‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplyCoordinate_ae r] with w hw
  change ‖multiplyCoordinate r w‖ ≤ _
  rw [hw, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [coordinate, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · linarith [le_max_left (-1 / 2 : ℝ) (min (1 / 2) w)]
  · exact max_le (by norm_num) (min_le_left _ _)

/-- The actual bounded multiplication operator M of §3.1, p.13. -/
def multiplicationOperator : BandSpace →L[ℂ] BandSpace :=
  coordinateLinear.mkContinuous (1 / 2) coordinateLinear_bound

end HamLocality237.Testing


