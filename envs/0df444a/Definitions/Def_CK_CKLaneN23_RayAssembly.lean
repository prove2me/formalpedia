-- Prove2me | Definitions.Def_CK_CKLaneN23_RayAssembly
-- name    : CK_CKLaneN23_RayAssembly
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-07T00:10:35.087795+00:00
-- url     : https://prove2.me/theorems/281b2e54-8694-4cd1-85dd-5aebbbe94344
-- title:
--   Courtade–Kumar proof module `CKLaneN23.RayAssembly` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.RayAssembly` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.RayAssembly` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.RayAssembly (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/RayAssembly.lean)

import Definitions.Def_CK_CKLaneN23_RayCalc
import Definitions.Def_CK_GeneralCK_PureGapE8Bridge
import Definitions.Def_CK_GeneralCK_RadialZeroBoundary
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
import Mathlib.Analysis.Complex.ExponentialBounds

-- ===== source module CKLaneN23.RayAssembly =====
section

/-!
# Lane N23 — RA-stat: ray limits, ray convexity, and the conditional assembly

* `rayRadial_tendsto_zero`, `rayPhi1_tendsto_zero`: `φ(0+) = 0`, `φ'(0+) = 0` (all `0 < b ≤ 1/2`).
* `ray_nonneg_of_gamma`: `rayGamma ≥ 0` on `(0,d0]` ⇒ `0 ≤ φ(d0)`.
* `rsValue_of_gamma`: `GammaCorner εc → GammaNonCorner S εc → RSValue S`.
* `rightStationary_of_gamma`: the exact capFibers field from the two certificate pieces (CONDITIONAL).
-/

namespace CKLaneN23.RS

open GeneralCK Filter Set
open scoped Topology

/-! ### the unit-entropy radial profile near the origin -/

theorem continuousAt_F1 {ζ : ℝ} (hζ : 0 ≤ ζ) : ContinuousAt (fun z => F z 1) ζ := by
  rcases hζ.lt_or_eq with h | h
  · exact (hasDerivAt_F_radius h one_pos).continuousAt
  · rw [← h]; exact (hasDerivAt_F_zero one_pos).continuousAt

theorem F_zero_left (h : ℝ) : F 0 h = 0 := by simp [F]

theorem tendsto_F_curve {l : Filter ℝ} {s e : ℝ → ℝ} {s0 e0 : ℝ}
    (hs : Tendsto s l (𝓝 s0)) (he : Tendsto e l (𝓝 e0)) (hs0 : 0 ≤ s0) (he0 : 0 < e0)
    (hepos : ∀ᶠ x in l, 0 < e x) :
    Tendsto (fun x => F (s x) (e x)) l (𝓝 (F s0 e0)) := by
  have hq : Tendsto (fun x => s x / e x) l (𝓝 (s0 / e0)) := hs.div he he0.ne'
  have hF : Tendsto (fun x => F (s x / e x) 1) l (𝓝 (F (s0 / e0) 1)) :=
    (continuousAt_F1 (div_nonneg hs0 he0.le)).tendsto.comp hq
  have hm := he.mul hF
  rw [F_perspective he0.ne' s0]
  refine hm.congr' ?_
  filter_upwards [hepos] with x hx
  exact (F_perspective hx.ne' (s x)).symm

/-- `F_z(ζ,1) ≤ 6ζ` for `0 < ζ ≤ 4/25` (the argument of Lane P's `theta_le_twelve`). -/
theorem Fz1_le {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 4 / 25) : deriv (fun r => F r 1) ζ ≤ 6 * ζ := by
  set v := radialContact ζ 1 with hvdef
  have hv0 : 0 < v := radialContact_pos hζ one_pos
  have hvh : v < 1 / 2 := radialContact_lt_half hζ one_pos
  have heq : ζ * H v = 1 * (1 - 2 * v) := radialContact_equation hζ one_pos
  have hv42 : (21 / 50 : ℝ) ≤ v := by
    rw [hvdef]
    apply (le_radialContact_iff hζ one_pos (by norm_num) (by norm_num)).2
    have hH := H_le_one (21 / 50 : ℝ)
    have hH0 : 0 ≤ H (21 / 50 : ℝ) := H_nonneg (by norm_num) (by norm_num)
    nlinarith
  set t := 1 - 2 * v with htdef
  have ht0 : 0 < t := by linarith
  have ht1 : t ≤ 4 / 25 := by linarith
  have hHv1 : H v ≤ 1 := H_le_one v
  have hlog2 : (6931 / 10000 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hL0 : 0 < Real.log 2 := by linarith
  have ht2 : 0 < 1 - t ^ 2 := by nlinarith
  have hJ : J v ≤ 2 * t / (1 - t ^ 2) / Real.log 2 := by
    have hratio : (1 - v) / v = (1 + t) / (1 - t) := by
      rw [htdef]; field_simp; ring
    unfold J
    rw [hratio]
    apply div_le_div_of_nonneg_right _ hL0.le
    have h := Real.log_div_le_sum_range_add ht0.le (by linarith : t < 1) 0
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add, pow_one] at h
    have e : 2 * t / (1 - t ^ 2) = 2 * (t / (1 - t ^ 2)) := by ring
    rw [e]; linarith
  have hk : Real.log 2 ≤ Certificates.Mixed.kap v := by
    unfold Certificates.Mixed.kap
    have hp : 0 < v * (1 - v) := mul_pos hv0 (by linarith)
    have hq : v * (1 - v) ≤ 1 / 4 := by nlinarith [sq_nonneg (v - 1 / 2)]
    have hl : Real.log (v * (1 - v)) ≤ Real.log (1 / 4) := Real.log_le_log hp hq
    have h4 : Real.log (1 / 4 : ℝ) = -(2 * Real.log 2) := by
      rw [show (1 / 4 : ℝ) = ((2 : ℝ) ^ 2)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
      push_cast; ring
    linarith
  have hkpos : 0 < Certificates.Mixed.kap v := by linarith
  have hhn : Certificates.Mixed.hn v ≤ Real.log 2 := by
    rw [Certificates.Mixed.hn_eq_H_mul_log]; nlinarith
  have hhn0 : 0 ≤ Certificates.Mixed.hn v := by
    rw [Certificates.Mixed.hn_eq_H_mul_log]
    exact mul_nonneg (H_nonneg hv0.le (by linarith)) hL0.le
  have hvv : 2 * v * (1 - v) = (1 - t ^ 2) / 2 := by rw [htdef]; ring
  have hT : (1 - 2 * v) * Certificates.Mixed.hn v / (2 * Real.log 2 * v * (1 - v) * Certificates.Mixed.kap v) ≤
      2 * t / (1 - t ^ 2) / Real.log 2 := by
    have hden : 2 * Real.log 2 * v * (1 - v) * Certificates.Mixed.kap v =
        Real.log 2 * Certificates.Mixed.kap v * ((1 - t ^ 2) / 2) := by
      rw [← hvv]; ring
    rw [hden, ← htdef]
    rw [div_le_div_iff₀ (by positivity) hL0]
    have e1 : t * Certificates.Mixed.hn v * Real.log 2 ≤ t * Real.log 2 * Real.log 2 := by
      have := mul_le_mul_of_nonneg_left hhn ht0.le
      nlinarith
    have e2 : t * Real.log 2 * Real.log 2 ≤ t * Real.log 2 * Certificates.Mixed.kap v := by
      have := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ t * Real.log 2)
      linarith
    have e3 : 2 * t / (1 - t ^ 2) * (Real.log 2 * Certificates.Mixed.kap v * ((1 - t ^ 2) / 2)) =
        t * Real.log 2 * Certificates.Mixed.kap v := by
      field_simp
    rw [e3]
    linarith
  rw [deriv_F_radius_slope hζ one_pos, ← hvdef]
  unfold radialSlope
  have hsum : J v + (1 - 2 * v) * Certificates.Mixed.hn v /
      (2 * Real.log 2 * v * (1 - v) * Certificates.Mixed.kap v) ≤ 4 * t / ((1 - t ^ 2) * Real.log 2) := by
    have e4 : 2 * t / (1 - t ^ 2) / Real.log 2 + 2 * t / (1 - t ^ 2) / Real.log 2 =
        4 * t / ((1 - t ^ 2) * Real.log 2) := by
      field_simp; ring
    linarith
  have hfin : 4 * t / ((1 - t ^ 2) * Real.log 2) ≤ 3 * t / (1 / 2) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have htt : t ^ 2 ≤ 16 / 625 := by nlinarith
    have h1 : (609 / 625 : ℝ) * (6931 / 10000) ≤ (1 - t ^ 2) * Real.log 2 :=
      mul_le_mul (by linarith) (le_of_lt hlog2) (by norm_num) (by linarith)
    nlinarith
  have ht6 : 3 * t / (1 / 2) ≤ 6 * ζ := by
    have : t ≤ ζ := by nlinarith [H_nonneg hv0.le (by linarith : v ≤ 1)]
    linarith
  linarith

theorem Fz1_nonneg {ζ : ℝ} (hζ : 0 < ζ) : 0 ≤ deriv (fun r => F r 1) ζ := by
  have h := e8Theta_pos (show 0 < ζ / 2 by positivity)
  unfold e8Theta at h
  rw [show 2 * (ζ / 2) = ζ by ring] at h
  exact h.le

theorem Fz1_zero : deriv (fun r => F r 1) 0 = 0 := (hasDerivAt_F_zero one_pos).deriv

theorem tendsto_Fz1 {l : Filter ℝ} {ζ : ℝ → ℝ} {ζ0 : ℝ} (hζ : Tendsto ζ l (𝓝 ζ0)) (hζ0 : 0 ≤ ζ0)
    (hpos : ∀ᶠ x in l, 0 < ζ x) :
    Tendsto (fun x => deriv (fun r => F r 1) (ζ x)) l (𝓝 (deriv (fun r => F r 1) ζ0)) := by
  rcases hζ0.lt_or_eq with h | h
  · exact (hasDerivAt_deriv_F_radius h one_pos).continuousAt.tendsto.comp hζ
  · rw [← h, Fz1_zero]
    rw [← h] at hζ
    have hup : Tendsto (fun x => 6 * ζ x) l (𝓝 0) := by simpa using hζ.const_mul 6
    have hsmall : ∀ᶠ x in l, ζ x ≤ 4 / 25 := hζ.eventually (ge_mem_nhds (by norm_num))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hpos] with x hx
      exact Fz1_nonneg hx
    · filter_upwards [hpos, hsmall] with x hx hx2
      exact Fz1_le hx hx2

theorem tendsto_perspectiveSlope {l : Filter ℝ} {s e ds de : ℝ → ℝ} {s0 e0 ds0 de0 : ℝ}
    (hs : Tendsto s l (𝓝 s0)) (he : Tendsto e l (𝓝 e0)) (hds : Tendsto ds l (𝓝 ds0))
    (hde : Tendsto de l (𝓝 de0)) (hs0 : 0 ≤ s0) (he0 : 0 < e0)
    (hspos : ∀ᶠ x in l, 0 < s x) (hepos : ∀ᶠ x in l, 0 < e x) :
    Tendsto (fun x => perspectiveSlope (s x) (e x) (ds x) (de x)) l
      (𝓝 (perspectiveSlope s0 e0 ds0 de0)) := by
  have hq : Tendsto (fun x => s x / e x) l (𝓝 (s0 / e0)) := hs.div he he0.ne'
  have hqpos : ∀ᶠ x in l, 0 < s x / e x := by
    filter_upwards [hspos, hepos] with x h1 h2
    exact div_pos h1 h2
  have hFz := tendsto_Fz1 hq (div_nonneg hs0 he0.le) hqpos
  have hF : Tendsto (fun x => F (s x / e x) 1) l (𝓝 (F (s0 / e0) 1)) :=
    (continuousAt_F1 (div_nonneg hs0 he0.le)).tendsto.comp hq
  unfold perspectiveSlope
  exact ((hds.sub (hq.mul hde)).mul hFz).add (hde.mul hF)

/-! ### `etaSlope` is bounded near maximal entropy -/

theorem etaSlope_bound {h : ℝ} (h0 : H (1 / 4) ≤ h) (h1 : h < 1) :
    |Scalar.etaSlope h| ≤ 8 := by
  have hh0 : 0 < h := lt_of_lt_of_le (H_pos (by norm_num) (by norm_num)) h0
  set m := entropyInverse h with hm
  have hm0 : 0 < m := entropyInverse_pos hh0 h1.le
  have hmh : m < 1 / 2 := entropyInverse_lt_half hh0.le h1
  have hm4 : 1 / 4 ≤ m := by
    have := entropyInverse_mono (H_nonneg (by norm_num) (by norm_num)) h1.le h0
    rwa [entropyInverse_H_lower (by norm_num) (by norm_num)] at this
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set y := 1 - 2 * m with hy
  have hy0 : 0 < y := by linarith
  have hy1 : y < 1 := by linarith
  -- J m ≥ y / log 2
  have hJ : y / Real.log 2 ≤ J m := by
    unfold J
    apply div_le_div_of_nonneg_right _ hL0.le
    have hr : (1 - m) / m = (1 + y) / (1 - y) := by rw [hy]; field_simp; ring
    rw [hr]
    have hpos : 0 < (1 - y) / (1 + y) := by apply div_pos <;> linarith
    have hl := Real.log_le_sub_one_of_pos hpos
    have hinv : Real.log ((1 + y) / (1 - y)) = -Real.log ((1 - y) / (1 + y)) := by
      rw [← Real.log_inv, inv_div]
    rw [hinv]
    have e : (1 - y) / (1 + y) - 1 = -(2 * y) / (1 + y) := by field_simp; ring
    rw [e] at hl
    have : y ≤ 2 * y / (1 + y) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have h2 : -(2 * y) / (1 + y) = -(2 * y / (1 + y)) := by ring
    linarith
  have hJpos : 0 < J m := lt_of_lt_of_le (by positivity) hJ
  have h1m : 0 < 1 - m := by linarith
  have hden : 0 < Real.log 2 * m * (1 - m) * J m := by positivity
  have hq2 : (1 - 2 * m) / (Real.log 2 * m * (1 - m) * J m) ≤ 6 := by
    rw [div_le_iff₀ hden]
    have hmm : 3 / 16 ≤ m * (1 - m) := by nlinarith
    have hA : y ≤ Real.log 2 * J m := by
      have := (div_le_iff₀ hL0).1 hJ; linarith
    have : y ≤ 6 * (Real.log 2 * m * (1 - m) * J m) := by
      have h6 : Real.log 2 * J m * (3 / 16) * 6 ≤ 6 * (Real.log 2 * m * (1 - m) * J m) := by
        have := mul_le_mul_of_nonneg_left hmm (by positivity : (0 : ℝ) ≤ Real.log 2 * J m)
        nlinarith
      nlinarith
    rw [← hy]; linarith
  have hq : 0 ≤ (1 - 2 * m) / (Real.log 2 * m * (1 - m) * J m) :=
    div_nonneg (by linarith) hden.le
  unfold Scalar.etaSlope
  rw [← hm, abs_le]
  constructor <;> linarith

/-! ### limits at the diagonal -/

section limits

variable {b t : ℝ}

theorem eta_H_closed {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 2) : eta (H b) = (1 - 2 * b) * J b := by
  rcases hb.lt_or_eq with h | h
  · exact Comparison.eta_H hb0 h
  · subst h
    rw [H_half, eta_one]
    norm_num

theorem F_cap_eq_eta {b : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 2) : F (1 - 2 * b) (H b) = eta (H b) := by
  have h := phi_at_entropy_cap hb0 hb
  unfold phi at h
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * b)] at h
  linarith

theorem etaSlope_H {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    Scalar.etaSlope (H b) = -2 - (1 - 2 * b) / (Real.log 2 * b * (1 - b) * J b) := by
  unfold Scalar.etaSlope
  rw [entropyInverse_H_lower hb0.le hb.le]

theorem ray_event (hb0 : 0 < b) : ∀ᶠ d in 𝓝[>] (0 : ℝ), d ∈ Ioo 0 b :=
  Ioo_mem_nhdsGT hb0

theorem tendsto_ray_id : Tendsto (fun d : ℝ => d) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds tendsto_id

theorem tendsto_ray_u (b : ℝ) : Tendsto (fun d : ℝ => b - d) (𝓝[>] (0 : ℝ)) (𝓝 b) := by
  have := (tendsto_const_nhds (x := b)).sub tendsto_ray_id
  simpa using this

theorem tendsto_ray_Hu (hb0 : 0 < b) (hb : b ≤ 1 / 2) :
    Tendsto (fun d : ℝ => H (b - d)) (𝓝[>] (0 : ℝ)) (𝓝 (H b)) :=
  (Comparison.hasDerivAt_H hb0 (by linarith)).continuousAt.tendsto.comp (tendsto_ray_u b)

theorem tendsto_ray_Ju (hb0 : 0 < b) (hb : b ≤ 1 / 2) :
    Tendsto (fun d : ℝ => J (b - d)) (𝓝[>] (0 : ℝ)) (𝓝 (J b)) :=
  (hasDerivAt_J_Jd1 hb0 (by linarith)).continuousAt.tendsto.comp (tendsto_ray_u b)

theorem tendsto_ray_Jd1u (hb0 : 0 < b) (hb : b ≤ 1 / 2) :
    Tendsto (fun d : ℝ => Jd1 (b - d)) (𝓝[>] (0 : ℝ)) (𝓝 (Jd1 b)) :=
  (hasDerivAt_Jd1 hb0 (by linarith)).continuousAt.tendsto.comp (tendsto_ray_u b)

theorem tendsto_rayE (hb0 : 0 < b) (hb : b ≤ 1 / 2) :
    Tendsto (fun d : ℝ => rayE b d) (𝓝[>] (0 : ℝ)) (𝓝 (H b)) := by
  have := ((tendsto_ray_Hu hb0 hb).add (tendsto_const_nhds (x := H b))).div_const 2
  simpa [rayE] using this

theorem rayE_event (hb0 : 0 < b) (hb : b ≤ 1 / 2) :
    ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < rayE b d ∧ rayE b d < 1 := by
  filter_upwards [ray_event hb0] with d hd
  exact ⟨rayE_pos hd.1 hd.2 hb, rayE_lt_one hd.1 hd.2 hb⟩

theorem Hu_event (hb0 : 0 < b) (hb : b ≤ 1 / 2) :
    ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < H (b - d) := by
  filter_upwards [ray_event hb0] with d hd
  exact ray_Hu_pos hd.1 hd.2 hb

theorem rayRadial_tendsto_zero (hb0 : 0 < b) (hb : b ≤ 1 / 2) (ht0 : 0 < t) :
    Tendsto (fun d => rayRadial b t d) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hHb := ray_Hb_pos hb0 hb
  have hE := tendsto_rayE hb0 hb
  have hEpos : ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < rayE b d := (rayE_event hb0 hb).mono fun _ h => h.1
  have hr : 0 ≤ 1 - 2 * b := by linarith
  have hd := tendsto_ray_id
  have hA : Tendsto (fun d => rayA b d) (𝓝[>] (0 : ℝ)) (𝓝 ((1 - 2 * b) * J b / 2)) := by
    have := ((((tendsto_const_nhds (x := 1 - 2 * b)).add (hd.const_mul 3)).mul (tendsto_ray_Ju hb0 hb)).sub
      (hd.mul_const (J b))).div_const 2
    simpa [rayA] using this
  have hF1 := tendsto_F_curve (hd.const_mul t) hE (by simp) hHb hEpos
  have hF2 := tendsto_F_curve hd hE (le_refl _) hHb hEpos
  have hF3 := tendsto_F_curve ((tendsto_const_nhds (x := 1 - 2 * b)).add (hd.const_mul t)) hE
    (by simpa using hr) hHb hEpos
  have hF4 := tendsto_F_curve ((tendsto_const_nhds (x := 1 - 2 * b)).add (hd.const_mul (2 * t)))
    (tendsto_ray_Hu hb0 hb) (by simpa using hr) hHb (Hu_event hb0 hb)
  have heta : Tendsto (fun d => eta (rayE b d)) (𝓝[>] (0 : ℝ)) (𝓝 (eta (H b))) := by
    have hc := Scalar.eta_continuousOn (H b) ⟨hHb, H_le_one b⟩
    apply hc.tendsto.comp
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hE, ?_⟩
    filter_upwards [rayE_event hb0 hb] with d hd
    exact ⟨hd.1, hd.2.le⟩
  have h := ((((hA.add hF1).sub hF2).add hF3).sub heta).sub (hF4.div_const 2)
  have hlim : (1 - 2 * b) * J b / 2 + F (t * 0) (H b) - F 0 (H b) + F (1 - 2 * b + t * 0) (H b)
      - eta (H b) - F (1 - 2 * b + 2 * t * 0) (H b) / 2 = 0 := by
    simp only [mul_zero, add_zero, F_zero_left]
    rw [F_cap_eq_eta hb0 hb, eta_H_closed hb0 hb]
    ring
  rw [hlim] at h
  refine h.congr' (Eventually.of_forall fun d => ?_)
  simp [rayRadial]

theorem rayPhi1_tendsto_zero (hb0 : 0 < b) (hb : b ≤ 1 / 2) (ht0 : 0 < t) :
    Tendsto (fun d => rayPhi1 b t d) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hHb := ray_Hb_pos hb0 hb
  have hE := tendsto_rayE hb0 hb
  have hEpos : ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < rayE b d := (rayE_event hb0 hb).mono fun _ h => h.1
  have hr : 0 ≤ 1 - 2 * b := by linarith
  have hd := tendsto_ray_id
  have hdpos : ∀ᶠ d in 𝓝[>] (0 : ℝ), 0 < d := (ray_event hb0).mono fun _ h => h.1
  have hJu := tendsto_ray_Ju hb0 hb
  have hE1 : Tendsto (fun d => -(J (b - d)) / 2) (𝓝[>] (0 : ℝ)) (𝓝 (-(J b) / 2)) :=
    hJu.neg.div_const 2
  have hA1 : Tendsto (fun d => (3 * J (b - d) - (1 - 2 * b + 3 * d) * Jd1 (b - d) - J b) / 2)
      (𝓝[>] (0 : ℝ)) (𝓝 ((3 * J b - (1 - 2 * b) * Jd1 b - J b) / 2)) := by
    have := (((hJu.const_mul 3).sub (((tendsto_const_nhds (x := 1 - 2 * b)).add (hd.const_mul 3)).mul
      (tendsto_ray_Jd1u hb0 hb))).sub (tendsto_const_nhds (x := J b))).div_const 2
    simpa using this
  have hP1 := tendsto_perspectiveSlope (ds := fun _ => t) (ds0 := t) (hd.const_mul t) hE
    tendsto_const_nhds hE1 (by simp) hHb (hdpos.mono fun d h => by positivity) hEpos
  have hP2 := tendsto_perspectiveSlope (ds := fun _ => (1 : ℝ)) (ds0 := 1) hd hE
    tendsto_const_nhds hE1 (le_refl _) hHb hdpos hEpos
  have hP3 := tendsto_perspectiveSlope (ds := fun _ => t) (ds0 := t)
    ((tendsto_const_nhds (x := 1 - 2 * b)).add (hd.const_mul t)) hE
    tendsto_const_nhds hE1 (by simpa using hr) hHb (hdpos.mono fun d h => by positivity) hEpos
  have hP4 := tendsto_perspectiveSlope (ds := fun _ => 2 * t) (ds0 := 2 * t)
    ((tendsto_const_nhds (x := 1 - 2 * b)).add (hd.const_mul (2 * t)))
    (tendsto_ray_Hu hb0 hb) tendsto_const_nhds hJu.neg (by simpa using hr) hHb
    (hdpos.mono fun d h => by positivity) (Hu_event hb0 hb)
  -- the eta-slope term
  have hES : Tendsto (fun d => Scalar.etaSlope (rayE b d) * (-(J (b - d)) / 2)) (𝓝[>] (0 : ℝ))
      (𝓝 (Scalar.etaSlope (H b) * (-(J b) / 2))) := by
    rcases hb.lt_or_eq with hlt | heq
    · have hHb1 : H b < 1 := by
        rw [← H_half]; exact H_strictMonoOn ⟨hb0.le, hlt.le⟩ ⟨by norm_num, le_rfl⟩ hlt
      exact ((Scalar.hasDerivAt_etaSlope hHb hHb1).continuousAt.tendsto.comp hE).mul hE1
    · subst heq
      have hJ0 : J (1 / 2) = 0 := by unfold J; norm_num
      rw [hJ0, neg_zero, zero_div, mul_zero]
      have hE1' : Tendsto (fun d => -(J (1 / 2 - d)) / 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have h := hE1
        rw [hJ0, neg_zero, zero_div] at h
        exact h
      have hH4 : H (1 / 4) < 1 := by
        rw [← H_half]; exact H_strictMonoOn ⟨by norm_num, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num)
      have hEbig : ∀ᶠ d in 𝓝[>] (0 : ℝ), H (1 / 4) ≤ rayE (1 / 2) d := by
        have h1 : Tendsto (fun d => rayE (1 / 2) d) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
          have h := hE
          rw [H_half] at h
          exact h
        exact h1.eventually (le_mem_nhds hH4)
      have hbd : ∀ᶠ d in 𝓝[>] (0 : ℝ), |Scalar.etaSlope (rayE (1 / 2) d)| ≤ 8 := by
        filter_upwards [hEbig, rayE_event hb0 hb] with d h1 h2
        exact etaSlope_bound h1 h2.2
      have hprod : Tendsto (fun d => Scalar.etaSlope (rayE (1 / 2) d) * (-(J (1 / 2 - d)) / 2))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hmaj : Tendsto (fun d => 8 * |-(J (1 / 2 - d)) / 2|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          simpa using (hE1'.abs).const_mul 8
        refine squeeze_zero_norm' ?_ hmaj
        filter_upwards [hbd] with d hd
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right hd (abs_nonneg _)
      exact hprod
  have h := ((((hA1.add hP1).sub hP2).add hP3).sub hES).sub (hP4.div_const 2)
  have hlim : (3 * J b - (1 - 2 * b) * Jd1 b - J b) / 2
      + perspectiveSlope (t * 0) (H b) t (-(J b) / 2) - perspectiveSlope 0 (H b) 1 (-(J b) / 2)
      + perspectiveSlope (1 - 2 * b + t * 0) (H b) t (-(J b) / 2)
      - Scalar.etaSlope (H b) * (-(J b) / 2)
      - perspectiveSlope (1 - 2 * b + 2 * t * 0) (H b) (2 * t) (-(J b)) / 2 = 0 := by
    simp only [mul_zero, add_zero]
    unfold perspectiveSlope
    simp only [zero_div, zero_mul, sub_zero, Fz1_zero, F_zero_left, mul_zero, add_zero]
    rcases hb.lt_or_eq with hlt | heq
    · rw [etaSlope_H hb0 hlt]
      have hJpos : 0 < J b := J_pos hb0 hlt
      have hb1 : 0 < 1 - b := by linarith
      have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      unfold Jd1
      field_simp
      ring
    · subst heq
      have hJ0 : J (1 / 2) = 0 := by unfold J; norm_num
      have h2 : (1 : ℝ) - 2 * (1 / 2) = 0 := by norm_num
      rw [hJ0, h2]
      simp only [zero_div, Fz1_zero, F_zero_left, neg_zero, mul_zero, zero_mul, sub_zero, add_zero,
        zero_add, zero_sub, neg_mul]
  rw [hlim] at h
  refine h.congr' (Eventually.of_forall fun d => ?_)
  simp [rayPhi1]

end limits

/-! ### convexity along the ray -/

theorem ray_nonneg_of_gamma {b t d0 : ℝ} (hb0 : 0 < b) (hb : b ≤ 1 / 2) (ht0 : 0 < t) (ht1 : t < 1)
    (hd0 : 0 < d0) (hd0b : d0 < b) (hG : ∀ d ∈ Ioc 0 d0, 0 ≤ rayGamma b t d) :
    0 ≤ canonicalPureGap (b - t * d0) b (H (b - d0)) (H b) := by
  rw [ray_eq_radial hb ht0 ht1 hd0 hd0b]
  have hderiv1 : ∀ d ∈ Ioc 0 d0, HasDerivAt (fun y => rayPhi1 b t y) (rayGamma b t d) d :=
    fun d hd => hasDerivAt_rayPhi1 hb ht0 ht1 hd.1 (lt_of_le_of_lt hd.2 hd0b)
  have hderiv0 : ∀ d ∈ Ioc 0 d0, HasDerivAt (fun y => rayRadial b t y) (rayPhi1 b t d) d :=
    fun d hd => hasDerivAt_rayRadial hb ht0 ht1 hd.1 (lt_of_le_of_lt hd.2 hd0b)
  have hconv : Convex ℝ (Ioc (0 : ℝ) d0) := convex_Ioc 0 d0
  have hint : interior (Ioc (0 : ℝ) d0) = Ioo 0 d0 := interior_Ioc
  -- rayPhi1 is monotone on (0, d0]
  have hmono1 : MonotoneOn (fun y => rayPhi1 b t y) (Ioc 0 d0) := by
    apply monotoneOn_of_deriv_nonneg hconv
    · exact fun d hd => (hderiv1 d hd).continuousAt.continuousWithinAt
    · rw [hint]; exact fun d hd => (hderiv1 d ⟨hd.1, hd.2.le⟩).differentiableAt.differentiableWithinAt
    · rw [hint]; intro d hd
      rw [(hderiv1 d ⟨hd.1, hd.2.le⟩).deriv]
      exact hG d ⟨hd.1, hd.2.le⟩
  have hphi1 : ∀ d ∈ Ioc 0 d0, 0 ≤ rayPhi1 b t d := by
    intro d hd
    have hlim := rayPhi1_tendsto_zero hb0 hb ht0
    apply le_of_tendsto hlim
    filter_upwards [Ioo_mem_nhdsGT hd.1] with y hy
    exact hmono1 ⟨hy.1, hy.2.le.trans hd.2⟩ hd hy.2.le
  have hmono0 : MonotoneOn (fun y => rayRadial b t y) (Ioc 0 d0) := by
    apply monotoneOn_of_deriv_nonneg hconv
    · exact fun d hd => (hderiv0 d hd).continuousAt.continuousWithinAt
    · rw [hint]; exact fun d hd => (hderiv0 d ⟨hd.1, hd.2.le⟩).differentiableAt.differentiableWithinAt
    · rw [hint]; intro d hd
      rw [(hderiv0 d ⟨hd.1, hd.2.le⟩).deriv]
      exact hphi1 d ⟨hd.1, hd.2.le⟩
  have hlim := rayRadial_tendsto_zero hb0 hb ht0
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT hd0] with y hy
  exact hmono0 ⟨hy.1, hy.2.le⟩ ⟨hd0, le_rfl⟩ hy.2.le

/-! ### assembly -/

/-- Value positivity from the two certificate pieces. -/
theorem rsValue_of_gamma {S εc : ℝ} (hC : GammaCorner εc) (hN : GammaNonCorner S εc) :
    RSValue S := by
  intro a x b ha hax hxb hb hS
  set d0 := b - a with hd0def
  set t := (b - x) / (b - a) with htdef
  have hd0 : 0 < d0 := by linarith
  have hd0b : d0 < b := by linarith
  have hb0 : 0 < b := by linarith
  have ht0 : 0 < t := div_pos (by linarith) (by linarith)
  have ht1 : t < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hx : b - t * d0 = x := by
    rw [htdef, hd0def, div_mul_cancel₀ _ (ne_of_gt (by linarith : (0 : ℝ) < b - a))]; ring
  have ha' : b - d0 = a := by rw [hd0def]; ring
  have key := ray_nonneg_of_gamma hb0 hb ht0 ht1 hd0 hd0b (fun d hd => by
    by_cases hc : (1 / 2 - b) + d ≤ εc
    · exact hC b t d ht0.le ht1.le hd.1 (lt_of_le_of_lt hd.2 hd0b) hb hc
    · push_neg at hc
      apply hN b t d ht0.le ht1.le hd.1 (lt_of_le_of_lt hd.2 hd0b) hb _ hc.le
      have : t * d ≤ t * d0 := mul_le_mul_of_nonneg_left hd.2 ht0.le
      linarith)
  rwa [hx, ha'] at key

/-- The exact capFibers field `rightStationary` at `retainedCutoff`, from the two certificate pieces
(CONDITIONAL on `GammaCorner εc` and `GammaNonCorner retainedCutoff εc`). -/
theorem rightStationary_of_gamma {εc : ℝ} (hC : GammaCorner εc)
    (hN : GammaNonCorner SmallMeanPhiCutoff.retainedCutoff εc) :
    RightStationaryField SmallMeanPhiCutoff.retainedCutoff :=
  rightStationaryField_of_prob (prob_of_value (rsValue_of_gamma hC hN))

end CKLaneN23.RS

end


