-- Prove2me | Definitions.Def_CK_CKLaneP_SeamK
-- name    : CK_CKLaneP_SeamK
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T12:53:55.572934+00:00
-- url     : https://prove2.me/theorems/5f0e20cd-209f-40cd-b735-0725072298eb
-- title:
--   Courtade–Kumar proof module `CKLaneP.SeamK` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneP.SeamK` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneP.SeamK` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneP.SeamK (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneP/SeamK.lean)

import Definitions.Def_CK_CKLaneP_SeamCore
import Definitions.Def_CK_CKLaneP_ThetaPrime

-- ===== source module CKLaneP.SeamK =====
section
/-
Lane P — the K-bound for stationary seam points.

Seam fiber `s(y) = seamCurve S e f y`, derivative `seamD S e f y = Θ(y/E) − Δ(y)`, `E = e + f`,
`Δ(y) = seamDelta S e f y = (Θ((1−S+y)/(2e)) − Θ((1−S−y)/(2f)))/2` (increasing in `y`).

`seam_kbound`: at a stationary point `y*` (`seamD S e f y* = 0`) and any `0 ≤ y0 < y*`,
    s(y*) ≥ s(y0) − (y*·Θ(y*/E) − F(y*, E/2)).
Proof: `kAux y = s(y) − F(y, E/2) + y·Δ(y*)` has derivative `Δ(y*) − Δ(y) ≥ 0` on `(y0, y*)`;
`Θ(y*/E) = Δ(y*)`; and `F(y0, E/2) ≤ y0·Θ(y0/E) ≤ y0·Δ(y*)` (convexity of `F`, monotonicity of Θ).

`dipK y = y·Θ(y/E) − F(y, E/2)` is the subtracted "dip"; bounds:
* `dipK_mono`   : increasing in `y > 0`;
* `dipK_quad`   : `dipK y ≤ (12 − ρ/2)·y²/E` when `y/E ≤ min(x̄, 2/25)`, `ρ = Θ(x̄)/x̄`;
* `dipK_eq`     : `dipK y = y·(radialSlope v − J v)`, `v = radialContact (2y/E) 1`.
-/

set_option autoImplicit false

namespace CKLaneP

open GeneralCK Set

noncomputable def seamDelta (S e f y : ℝ) : ℝ :=
  (e8Theta ((1 - S + y) / (2 * e)) - e8Theta ((1 - S - y) / (2 * f))) / 2

theorem seamD_eq_sub (S e f y : ℝ) :
    seamD S e f y = e8Theta (y / (e + f)) - seamDelta S e f y := by
  unfold seamD seamDelta; ring

theorem e8Theta_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : e8Theta x ≤ e8Theta y :=
  strictMonoOn_e8Theta_pos.monotoneOn (show x ∈ Ioi (0 : ℝ) from hx)
    (show y ∈ Ioi (0 : ℝ) from lt_of_lt_of_le hx hxy) hxy

theorem e8Theta_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ e8Theta x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, e8Theta_zero]
  · exact (e8Theta_pos h).le

theorem e8Theta_mono0 {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : e8Theta x ≤ e8Theta y := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, e8Theta_zero]; exact e8Theta_nonneg (hx.trans hxy)
  · exact e8Theta_mono h hxy

theorem seamDelta_mono {S e f y1 y2 : ℝ} (he : 0 < e) (hf : 0 < f)
    (h1 : 0 < 1 - S + y1) (h12 : y1 ≤ y2) (h2 : 0 < 1 - S - y2) :
    seamDelta S e f y1 ≤ seamDelta S e f y2 := by
  unfold seamDelta
  have he2 : 0 < 2 * e := by linarith
  have hf2 : 0 < 2 * f := by linarith
  have ha : e8Theta ((1 - S + y1) / (2 * e)) ≤ e8Theta ((1 - S + y2) / (2 * e)) :=
    e8Theta_mono (div_pos h1 he2) (div_le_div_of_nonneg_right (by linarith) he2.le)
  have hb : e8Theta ((1 - S - y2) / (2 * f)) ≤ e8Theta ((1 - S - y1) / (2 * f)) :=
    e8Theta_mono (div_pos h2 hf2) (div_le_div_of_nonneg_right (by linarith) hf2.le)
  linarith

theorem F_zero_left (h : ℝ) : F 0 h = 0 := by simp [F]

theorem hasDerivAt_F_theta {y h : ℝ} (hy : 0 < y) (hh : 0 < h) :
    HasDerivAt (fun r => F r h) (e8Theta (y / (2 * h))) y := by
  have h1 := (hasDerivAt_F_radius hy hh).differentiableAt.hasDerivAt
  rwa [deriv_F_radius_eq_e8Theta hy hh] at h1

/-- `F(y, h) ≤ y·Θ(y/(2h))` (convexity of `F` in the radius, `F(0,h) = 0`). -/
theorem F_le_mul_theta {y h : ℝ} (hy : 0 ≤ y) (hh : 0 < h) :
    F y h ≤ y * e8Theta (y / (2 * h)) := by
  rcases hy.eq_or_lt with h0 | hpos
  · rw [← h0, F_zero_left]; simp
  · have hconv := convexOn_F_radius hh
    have hdiff := (hasDerivAt_F_radius hpos hh).differentiableAt
    have hsl := hconv.slope_le_deriv (Set.mem_Ici.mpr (le_refl (0 : ℝ)))
      (Set.mem_Ici.mpr hpos.le) hpos hdiff
    rw [deriv_F_radius_eq_e8Theta hpos hh] at hsl
    simp only [slope_def_field, F_zero_left, sub_zero] at hsl
    rw [div_le_iff₀ hpos] at hsl
    linarith

/-! ### The K-bound -/

noncomputable def kAux (S e f ys y : ℝ) : ℝ :=
  seamCurve S e f y - F y ((e + f) / 2) + y * seamDelta S e f ys

theorem hasDerivAt_kAux {S e f ys y : ℝ} (hS : 0 ≤ S) (he : 0 < e) (hf : 0 < f) (hy : 0 < y)
    (hS1 : S + y < 1) :
    HasDerivAt (kAux S e f ys) (seamD S e f y - e8Theta (y / (e + f)) + seamDelta S e f ys) y := by
  have hh : 0 < (e + f) / 2 := by linarith
  have h1 := hasDerivAt_seamCurve hy hS1 (by linarith) he hf
  have h2 := hasDerivAt_F_theta hy hh
  have e2 : y / (2 * ((e + f) / 2)) = y / (e + f) := by ring_nf
  rw [e2] at h2
  have h3 := (hasDerivAt_id y).mul_const (seamDelta S e f ys)
  have h4 := (h1.sub h2).add h3
  refine h4.congr_deriv ?_
  rw [one_mul]

theorem seam_kbound {S e f y0 ys : ℝ} (hS : 0 ≤ S) (he : 0 < e) (hf : 0 < f)
    (hy0 : 0 ≤ y0) (h0s : y0 < ys) (hS1 : S + ys < 1)
    (hstat : seamD S e f ys = 0) :
    seamCurve S e f y0 - (ys * e8Theta (ys / (e + f)) - F ys ((e + f) / 2)) ≤
      seamCurve S e f ys := by
  have hE0 : 0 < e + f := by linarith
  have hh : 0 < (e + f) / 2 := by linarith
  have hys : 0 < ys := lt_of_le_of_lt hy0 h0s
  have hTD : e8Theta (ys / (e + f)) = seamDelta S e f ys := by
    have h := seamD_eq_sub S e f ys
    rw [hstat] at h
    linarith
  have hcont : ContinuousOn (kAux S e f ys) (Icc y0 ys) := by
    have h1 : ContinuousOn (seamCurve S e f) (Icc y0 ys) :=
      (continuousOn_seamCurve hS1 hys.le he hf).mono (Icc_subset_Icc hy0 le_rfl)
    have h2 : ContinuousOn (fun y => F y ((e + f) / 2)) (Icc y0 ys) :=
      (continuousOn_F_radius hh).mono (fun y hy => (show y ∈ Ici (0 : ℝ) from hy0.trans hy.1))
    have h3 : ContinuousOn (fun y : ℝ => y * seamDelta S e f ys) (Icc y0 ys) :=
      continuousOn_id.mul continuousOn_const
    exact (h1.sub h2).add h3
  have hmono : MonotoneOn (kAux S e f ys) (Icc y0 ys) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y0 ys) hcont
    · intro y hy
      rw [interior_Icc] at hy
      have hy0' : 0 < y := lt_of_le_of_lt hy0 hy.1
      exact (hasDerivAt_kAux hS he hf hy0' (by linarith [hy.2])).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      have hy0' : 0 < y := lt_of_le_of_lt hy0 hy.1
      rw [(hasDerivAt_kAux hS he hf hy0' (by linarith [hy.2])).deriv, seamD_eq_sub]
      have hm := seamDelta_mono (S := S) he hf (by linarith) hy.2.le (by linarith)
      linarith
  have key := hmono ⟨le_rfl, h0s.le⟩ ⟨h0s.le, le_rfl⟩ h0s.le
  unfold kAux at key
  have hF0 : F y0 ((e + f) / 2) ≤ y0 * e8Theta (y0 / (e + f)) := by
    have h := F_le_mul_theta hy0 hh
    have e2 : y0 / (2 * ((e + f) / 2)) = y0 / (e + f) := by ring_nf
    rwa [e2] at h
  have hT : e8Theta (y0 / (e + f)) ≤ seamDelta S e f ys := by
    rw [← hTD]
    exact e8Theta_mono0 (div_nonneg hy0 hE0.le) (div_le_div_of_nonneg_right h0s.le hE0.le)
  have hT2 : y0 * e8Theta (y0 / (e + f)) ≤ y0 * seamDelta S e f ys :=
    mul_le_mul_of_nonneg_left hT hy0
  rw [hTD]
  linarith

/-! ### The dip term `dipK y = y·Θ(y/E) − F(y, E/2)` -/

noncomputable def dipK (E y : ℝ) : ℝ := y * e8Theta (y / E) - F y (E / 2)

theorem seam_kbound' {S e f y0 ys : ℝ} (hS : 0 ≤ S) (he : 0 < e) (hf : 0 < f)
    (hy0 : 0 ≤ y0) (h0s : y0 < ys) (hS1 : S + ys < 1)
    (hstat : seamD S e f ys = 0) :
    seamCurve S e f y0 - dipK (e + f) ys ≤ seamCurve S e f ys :=
  seam_kbound hS he hf hy0 h0s hS1 hstat

theorem dipK_mono {E y1 y2 : ℝ} (hE : 0 < E) (hy1 : 0 < y1) (h12 : y1 ≤ y2) :
    dipK E y1 ≤ dipK E y2 := by
  have hh : 0 < E / 2 := by linarith
  have hd : ∀ y ∈ Icc y1 y2, HasDerivAt (dipK E) (y * (deriv e8Theta (y / E) * (1 / E))) y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hy1 hy.1
    have hyE : 0 < y / E := div_pos hy0 hE
    have hT : HasDerivAt (fun t => e8Theta (t / E)) (deriv e8Theta (y / E) * (1 / E)) y := by
      have h1 := (hasDerivAt_e8Theta hyE).differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun t : ℝ => t / E) (1 / E) y := by
        simpa using (hasDerivAt_id y).div_const E
      have hT0 := h1.comp y h2
      exact hT0
    have hF := hasDerivAt_F_theta hy0 hh
    have e2 : y / (2 * (E / 2)) = y / E := by ring_nf
    rw [e2] at hF
    have h := ((hasDerivAt_id y).mul hT).sub hF
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hcont : ContinuousOn (dipK E) (Icc y1 y2) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hmono : MonotoneOn (dipK E) (Icc y1 y2) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc y1 y2) hcont
    · intro y hy
      exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      have hy' := interior_subset hy
      rw [(hd y hy').deriv]
      have hy0 : 0 < y := lt_of_lt_of_le hy1 hy'.1
      have hpos := deriv_e8Theta_pos (div_pos hy0 hE)
      have : 0 ≤ 1 / E := by positivity
      positivity
  exact hmono ⟨le_rfl, h12⟩ ⟨h12, le_rfl⟩ h12

/-- Quadratic dip bound for small `y/E`. -/
theorem dipK_quad {E y xb : ℝ} (hE : 0 < E) (hy : 0 < y) (hxb : y / E ≤ xb)
    (hsmall : y / E ≤ 2 / 25) :
    dipK E y ≤ (12 - e8Theta xb / xb / 2) * y ^ 2 / E := by
  have hh : 0 < E / 2 := by linarith
  have hyE : 0 < y / E := div_pos hy hE
  have hxb0 : 0 < xb := lt_of_lt_of_le hyE hxb
  set ρ := e8Theta xb / xb with hρ
  -- Θ(y/E) ≤ 12 y/E
  have h12 : e8Theta (y / E) ≤ 12 * (y / E) := theta_le_twelve hyE hsmall
  -- F(y, E/2) ≥ ρ y²/(2E): φ(t) = F(t,E/2) − ρ t²/(2E) is monotone on [0, y]
  have hφd : ∀ t ∈ Ioo 0 y, HasDerivAt (fun t => F t (E / 2) - ρ * t ^ 2 / (2 * E))
      (e8Theta (t / E) - ρ * t / E) t := by
    intro t ht
    have hF := hasDerivAt_F_theta ht.1 hh
    have e2 : t / (2 * (E / 2)) = t / E := by ring_nf
    rw [e2] at hF
    have hq := (((hasDerivAt_id t).pow 2).const_mul ρ).div_const (2 * E)
    refine (hF.sub hq).congr_deriv ?_
    simp only [id_eq, Nat.cast_ofNat]
    field_simp
    ring
  have hφc : ContinuousOn (fun t => F t (E / 2) - ρ * t ^ 2 / (2 * E)) (Icc 0 y) := by
    apply ContinuousOn.sub
    · exact (continuousOn_F_radius hh).mono (fun t ht => (show t ∈ Ici (0 : ℝ) from ht.1))
    · fun_prop
  have hφm : MonotoneOn (fun t => F t (E / 2) - ρ * t ^ 2 / (2 * E)) (Icc 0 y) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 y) hφc
    · intro t ht
      rw [interior_Icc] at ht
      exact (hφd t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hφd t ht).deriv]
      have htE : 0 < t / E := div_pos ht.1 hE
      have htx : t / E ≤ xb := le_trans (div_le_div_of_nonneg_right ht.2.le hE.le) hxb
      have hr := theta_ge_ratio htE htx
      have e3 : t / E * (e8Theta xb / xb) = ρ * t / E := by rw [hρ]; ring
      linarith
  have hφ := hφm ⟨le_rfl, hy.le⟩ ⟨hy.le, le_rfl⟩ hy.le
  simp only [F_zero_left] at hφ
  have hFlow : ρ * y ^ 2 / (2 * E) ≤ F y (E / 2) := by
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this, mul_zero, zero_div, sub_zero] at hφ
    linarith
  unfold dipK
  have h1 : y * e8Theta (y / E) ≤ y * (12 * (y / E)) := mul_le_mul_of_nonneg_left h12 hy.le
  have e4 : y * (12 * (y / E)) = 12 * y ^ 2 / E := by ring
  have e5 : (12 - ρ / 2) * y ^ 2 / E = 12 * y ^ 2 / E - ρ * y ^ 2 / (2 * E) := by
    ring
  rw [e5]
  linarith

end CKLaneP

end


