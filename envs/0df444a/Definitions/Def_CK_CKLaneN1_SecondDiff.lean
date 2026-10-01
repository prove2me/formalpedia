-- Prove2me | Definitions.Def_CK_CKLaneN1_SecondDiff
-- name    : CK_CKLaneN1_SecondDiff
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T09:31:27.363257+00:00
-- url     : https://prove2.me/theorems/01066583-316b-4954-9834-92b4ad71b341
-- title:
--   Courtade–Kumar proof module `CKLaneN1.SecondDiff` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN1.SecondDiff` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN1.SecondDiff` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN1.SecondDiff (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN1/SecondDiff.lean)

import Definitions.Def_CK_CKLaneN1_Analytic

-- ===== source module CKLaneN1.SecondDiff =====
section

/-!
# Lane N1: the second difference of `C(r) = 1 − H((1−r)/2)` (NO_SEP PROOF.md (15), `K₂`)

`Δ = [C(q+d) + C(q−d)]/2 − C(q)` for canonical laws (`q = 1−a−b`, `d = b−a`). The archive bounds
`Δ/d² ≤ K₂ = [C(q₊+D) + C(q₊−D) − 2C(q₊)]/(2D²)` using monotonicity of the second difference in
both `d` and `q`. It justifies this by a positive power series. Here the same monotonicity is proved
from `C'' = 1/(L(1−r²))` and convexity of `φ(r) = 1/(1−r²)`, with no series:

* `secondDiff_div_sq_le` : `h_q(d)/d² ≤ h_q(D)/D²` for `0 < d ≤ D` (convexity of `σ ↦ h_q(√σ)`);
* `secondDiff_mono_q`    : `h_q(D) ≤ h_{q₁}(D)` for `0 ≤ q ≤ q₁`.
-/

namespace CKLaneN1

open GeneralCK Set

/-- `C(r) = 1 − H((1−r)/2)`. -/
noncomputable def Cf (r : ℝ) : ℝ := 1 - H ((1 - r) / 2)

/-- `C'(r) = (log(1+r) − log(1−r))/(2L)`. -/
noncomputable def Cd (r : ℝ) : ℝ := (Real.log (1 + r) - Real.log (1 - r)) / (2 * Real.log 2)

/-- `φ(r) = 1/(1−r²)`. -/
noncomputable def phiC (r : ℝ) : ℝ := 1 / (1 - r ^ 2)

theorem Cf_neg (r : ℝ) : Cf (-r) = Cf r := by
  unfold Cf
  rw [show (1 - -r) / 2 = 1 - (1 - r) / 2 by ring, H_complement]

theorem Cd_neg (r : ℝ) : Cd (-r) = -Cd r := by
  unfold Cd
  rw [show (1 : ℝ) + -r = 1 - r by ring, show (1 : ℝ) - -r = 1 + r by ring]
  ring

theorem Cf_continuous : Continuous Cf := by
  unfold Cf
  exact continuous_const.sub (H_continuous.comp ((continuous_const.sub continuous_id).div_const 2))

theorem hasDerivAt_Cf {r : ℝ} (h0 : -1 < r) (h1 : r < 1) : HasDerivAt Cf (Cd r) r := by
  have hp0 : (1 - r) / 2 ≠ 0 := by intro h; linarith
  have hp1 : (1 - r) / 2 ≠ 1 := by intro h; linarith
  have hB := Real.hasDerivAt_binEntropy hp0 hp1
  have hin : HasDerivAt (fun x : ℝ => (1 - x) / 2) (-1 / 2) r :=
    ((hasDerivAt_id' r).const_sub 1).div_const 2
  have hc := (hB.comp r hin).div_const (Real.log 2)
  have hC : HasDerivAt (fun x : ℝ => 1 - Real.binEntropy ((1 - x) / 2) / Real.log 2)
      (-((Real.log (1 - (1 - r) / 2) - Real.log ((1 - r) / 2)) * (-1 / 2) / Real.log 2)) r :=
    hc.const_sub 1
  have hX : Real.log (1 - (1 - r) / 2) - Real.log ((1 - r) / 2) =
      Real.log (1 + r) - Real.log (1 - r) := by
    have e1 : 1 - (1 - r) / 2 = (1 + r) / 2 := by ring
    rw [e1, Real.log_div (by linarith) (by norm_num), Real.log_div (by linarith) (by norm_num)]
    ring
  have hval : -((Real.log (1 - (1 - r) / 2) - Real.log ((1 - r) / 2)) * (-1 / 2) / Real.log 2) =
      Cd r := by
    rw [hX]
    unfold Cd
    have hL := log_two_pos
    field_simp
  rw [hval] at hC
  exact hC

theorem hasDerivAt_Cd {r : ℝ} (h0 : -1 < r) (h1 : r < 1) :
    HasDerivAt Cd (phiC r / Real.log 2) r := by
  have e1 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + r)) r := by
    have := ((hasDerivAt_id' r).const_add 1).log (by linarith)
    simpa using this
  have e2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-(1 / (1 - r))) r := by
    have := ((hasDerivAt_id' r).const_sub 1).log (by linarith)
    have e : (-1 : ℝ) / (1 - r) = -(1 / (1 - r)) := by ring
    rw [e] at this
    exact this
  have hd := (e1.sub e2).div_const (2 * Real.log 2)
  have hval : (1 / (1 + r) - -(1 / (1 - r))) / (2 * Real.log 2) = phiC r / Real.log 2 := by
    unfold phiC
    have ha : (1 + r) ≠ 0 := by linarith
    have hb : (1 - r) ≠ 0 := by linarith
    have hc : 1 - r ^ 2 ≠ 0 := by nlinarith
    field_simp
    ring
  rw [hval] at hd
  exact hd

/-- Partial fractions: `φ(q+s) + φ(q−s) = X/(X²−s²) + Y/(Y²−s²)`, `X = 1−q`, `Y = 1+q`. -/
theorem phiC_sym_eq {q s : ℝ} (h1 : q + s < 1) (h2 : -1 < q - s) (h3 : q - s < 1) (h4 : -1 < q + s) :
    phiC (q + s) + phiC (q - s) =
      (1 - q) / ((1 - q) ^ 2 - s ^ 2) + (1 + q) / ((1 + q) ^ 2 - s ^ 2) := by
  unfold phiC
  have a1 : 1 - (q + s) ^ 2 ≠ 0 := by nlinarith
  have a2 : 1 - (q - s) ^ 2 ≠ 0 := by nlinarith
  have a3 : (1 - q) ^ 2 - s ^ 2 ≠ 0 := by nlinarith
  have a4 : (1 + q) ^ 2 - s ^ 2 ≠ 0 := by nlinarith
  field_simp
  ring

/-- Majorization: `t ↦ φ(q+t) + φ(q−t)` is monotone on `[0, D]`. -/
theorem phiC_sym_mono {q D s t : ℝ} (hqD : q + D < 1) (hqD' : -1 < q - D)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ D) :
    phiC (q + s) + phiC (q - s) ≤ phiC (q + t) + phiC (q - t) := by
  rw [phiC_sym_eq (by linarith) (by linarith) (by linarith) (by linarith),
    phiC_sym_eq (by linarith) (by linarith) (by linarith) (by linarith)]
  have hX : 0 < 1 - q := by linarith
  have hY : 0 < 1 + q := by linarith
  have hXt : 0 < (1 - q) ^ 2 - t ^ 2 := by nlinarith
  have hYt : 0 < (1 + q) ^ 2 - t ^ 2 := by nlinarith
  have hst2 : s ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hs hst 2
  have e1 : (1 - q) / ((1 - q) ^ 2 - s ^ 2) ≤ (1 - q) / ((1 - q) ^ 2 - t ^ 2) :=
    div_le_div_of_nonneg_left hX.le hXt (by linarith)
  have e2 : (1 + q) / ((1 + q) ^ 2 - s ^ 2) ≤ (1 + q) / ((1 + q) ^ 2 - t ^ 2) :=
    div_le_div_of_nonneg_left hY.le hYt (by linarith)
  linarith

/-- The function `A(t) = C'(q+t) − C'(q−t)` is convex on `[0, D]`. -/
theorem A_convexOn {q D : ℝ} (hqD : q + D < 1) (hqD' : -1 < q - D) (hD : 0 ≤ D) :
    ConvexOn ℝ (Icc 0 D) (fun t => Cd (q + t) - Cd (q - t)) := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 D)
  · intro t ht
    have h1 : -1 < q + t := by linarith [ht.1]
    have h2 : q + t < 1 := by linarith [ht.2]
    have h3 : -1 < q - t := by linarith [ht.2]
    have h4 : q - t < 1 := by linarith [ht.1]
    have d1 := (hasDerivAt_Cd h1 h2).comp t ((hasDerivAt_id' t).const_add q)
    have d2 := (hasDerivAt_Cd h3 h4).comp t ((hasDerivAt_id' t).const_sub q)
    exact (d1.continuousAt.sub d2.continuousAt).continuousWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    have h1 : -1 < q + t := by linarith [ht.1]
    have h2 : q + t < 1 := by linarith [ht.2]
    have h3 : -1 < q - t := by linarith [ht.2]
    have h4 : q - t < 1 := by linarith [ht.1]
    have d1 := (hasDerivAt_Cd h1 h2).comp t ((hasDerivAt_id' t).const_add q)
    have d2 := (hasDerivAt_Cd h3 h4).comp t ((hasDerivAt_id' t).const_sub q)
    exact (d1.sub d2).differentiableAt.differentiableWithinAt
  · have hderiv : ∀ t ∈ interior (Icc (0 : ℝ) D),
        deriv (fun t => Cd (q + t) - Cd (q - t)) t = (phiC (q + t) + phiC (q - t)) / Real.log 2 := by
      intro t ht
      rw [interior_Icc] at ht
      have h1 : -1 < q + t := by linarith [ht.1]
      have h2 : q + t < 1 := by linarith [ht.2]
      have h3 : -1 < q - t := by linarith [ht.2]
      have h4 : q - t < 1 := by linarith [ht.1]
      have d1 := (hasDerivAt_Cd h1 h2).comp t ((hasDerivAt_id' t).const_add q)
      have d2 := (hasDerivAt_Cd h3 h4).comp t ((hasDerivAt_id' t).const_sub q)
      have hd : HasDerivAt (fun t => Cd (q + t) - Cd (q - t))
          (phiC (q + t) / Real.log 2 * 1 - phiC (q - t) / Real.log 2 * (-1)) t := d1.sub d2
      rw [hd.deriv]
      ring
    intro s hs t ht hst
    rw [hderiv s hs, hderiv t ht]
    rw [interior_Icc] at hs ht
    exact div_le_div_of_nonneg_right
      (phiC_sym_mono hqD hqD' hs.1.le hst ht.2.le) log_two_pos.le

/-- `A(t)/t ≤ A(s)/s` for `0 < t ≤ s ≤ D`, in product form. -/
theorem A_slope {q D s t : ℝ} (hqD : q + D < 1) (hqD' : -1 < q - D)
    (ht : 0 < t) (hts : t ≤ s) (hs : s ≤ D) :
    s * (Cd (q + t) - Cd (q - t)) ≤ t * (Cd (q + s) - Cd (q - s)) := by
  have hD : 0 ≤ D := ht.le.trans (hts.trans hs)
  have hconv := A_convexOn hqD hqD' hD
  have hspos : 0 < s := ht.trans_le hts
  have hc := hconv.2 (show (0 : ℝ) ∈ Icc 0 D from ⟨le_rfl, hD⟩) (show s ∈ Icc 0 D from ⟨hspos.le, hs⟩)
    (show (0 : ℝ) ≤ 1 - t / s by rw [sub_nonneg, div_le_one hspos]; exact hts)
    (show (0 : ℝ) ≤ t / s by positivity) (by ring)
  have e : (1 - t / s) * 0 + t / s * s = t := by
    rw [mul_zero, zero_add, div_mul_cancel₀ _ hspos.ne']
  have e0 : Cd (q + 0) - Cd (q - 0) = 0 := by simp
  simp only [smul_eq_mul] at hc
  rw [e, e0, mul_zero, zero_add] at hc
  have := mul_le_mul_of_nonneg_left hc hspos.le
  rw [show s * (t / s * (Cd (q + s) - Cd (q - s))) = t * (Cd (q + s) - Cd (q - s)) by
    field_simp] at this
  exact this

/-- The second difference `h_q(d) = C(q+d) + C(q−d) − 2C(q)`. -/
noncomputable def secondDiff (q d : ℝ) : ℝ := Cf (q + d) + Cf (q - d) - 2 * Cf q

/-- Monotonicity in `d`: `h_q(d)/d² ≤ h_q(D)/D²` for `0 < d ≤ D`, in product form. -/
theorem secondDiff_div_sq_le {q D d : ℝ} (hqD : q + D < 1) (hqD' : -1 < q - D)
    (hd : 0 < d) (hdD : d ≤ D) :
    D ^ 2 * secondDiff q d ≤ d ^ 2 * secondDiff q D := by
  have hDpos : 0 < D := hd.trans_le hdD
  -- k(σ) = h(√σ) is convex on [0, D²]
  set k : ℝ → ℝ := fun σ => secondDiff q (Real.sqrt σ) with hk
  have hkcont : ContinuousOn k (Icc 0 (D ^ 2)) := by
    have hc : Continuous k := by
      simp only [hk, secondDiff]
      exact ((Cf_continuous.comp (continuous_const.add Real.continuous_sqrt)).add
        (Cf_continuous.comp (continuous_const.sub Real.continuous_sqrt))).sub continuous_const
    exact hc.continuousOn
  have hkderiv : ∀ σ ∈ Ioo 0 (D ^ 2), HasDerivAt k
      ((Cd (q + Real.sqrt σ) - Cd (q - Real.sqrt σ)) / (2 * Real.sqrt σ)) σ := by
    intro σ hσ
    have hσ0 : 0 < σ := hσ.1
    have hs := Real.sqrt_pos.mpr hσ0
    have hsD : Real.sqrt σ < D := by
      rw [Real.sqrt_lt' hDpos]
      exact hσ.2
    have h1 : -1 < q + Real.sqrt σ := by linarith
    have h2 : q + Real.sqrt σ < 1 := by linarith
    have h3 : -1 < q - Real.sqrt σ := by linarith
    have h4 : q - Real.sqrt σ < 1 := by linarith
    have hsq := Real.hasDerivAt_sqrt hσ0.ne'
    have d1 := (hasDerivAt_Cf h1 h2).comp σ (hsq.const_add q)
    have d2 := (hasDerivAt_Cf h3 h4).comp σ (hsq.const_sub q)
    have hd := (d1.add d2).sub_const (2 * Cf q)
    have hval : Cd (q + Real.sqrt σ) * (1 / (2 * Real.sqrt σ)) +
        Cd (q - Real.sqrt σ) * -(1 / (2 * Real.sqrt σ)) =
        (Cd (q + Real.sqrt σ) - Cd (q - Real.sqrt σ)) / (2 * Real.sqrt σ) := by ring
    rw [hval] at hd
    exact hd
  have hkconv : ConvexOn ℝ (Icc 0 (D ^ 2)) k := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 (D ^ 2)) hkcont
    · intro σ hσ
      rw [interior_Icc] at hσ
      exact (hkderiv σ hσ).differentiableAt.differentiableWithinAt
    · intro σ₁ hσ₁ σ₂ hσ₂ hle
      rw [interior_Icc] at hσ₁ hσ₂
      rw [(hkderiv σ₁ hσ₁).deriv, (hkderiv σ₂ hσ₂).deriv]
      have hs1 := Real.sqrt_pos.mpr hσ₁.1
      have hs2 := Real.sqrt_pos.mpr hσ₂.1
      have hs12 : Real.sqrt σ₁ ≤ Real.sqrt σ₂ := Real.sqrt_le_sqrt hle
      have hs2D : Real.sqrt σ₂ ≤ D := by
        rw [Real.sqrt_le_left hDpos.le]; exact hσ₂.2.le
      have hsl := A_slope hqD hqD' hs1 hs12 hs2D
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  -- secant from 0
  have hk0 : k 0 = 0 := by
    simp only [hk, secondDiff, Real.sqrt_zero, add_zero, sub_zero]
    ring
  have hd2 : 0 < d ^ 2 := by positivity
  have hD2 : 0 < D ^ 2 := by positivity
  have hdD2 : d ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hd.le hdD 2
  have hc := hkconv.2 (show (0 : ℝ) ∈ Icc 0 (D ^ 2) from ⟨le_rfl, hD2.le⟩)
    (show D ^ 2 ∈ Icc 0 (D ^ 2) from ⟨hD2.le, le_rfl⟩)
    (show (0 : ℝ) ≤ 1 - d ^ 2 / D ^ 2 by rw [sub_nonneg, div_le_one hD2]; exact hdD2)
    (show (0 : ℝ) ≤ d ^ 2 / D ^ 2 by positivity) (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, hk0] at hc
  have e : d ^ 2 / D ^ 2 * D ^ 2 = d ^ 2 := by field_simp
  rw [e] at hc
  have hkd : k (d ^ 2) = secondDiff q d := by
    simp only [hk, Real.sqrt_sq hd.le]
  have hkD : k (D ^ 2) = secondDiff q D := by
    simp only [hk, Real.sqrt_sq hDpos.le]
  rw [hkd, hkD] at hc
  have := mul_le_mul_of_nonneg_left hc hD2.le
  rw [show D ^ 2 * (d ^ 2 / D ^ 2 * secondDiff q D) = d ^ 2 * secondDiff q D by field_simp] at this
  exact this

/-- Monotonicity in `q`: `h_q(D) ≤ h_{q₁}(D)` for `0 ≤ q ≤ q₁`, `q₁ + D < 1`, `0 ≤ D < 1`. -/
theorem secondDiff_mono_q {q q₁ D : ℝ} (hq : 0 ≤ q) (hqq : q ≤ q₁) (hq₁ : q₁ + D < 1)
    (hD : 0 ≤ D) :
    secondDiff q D ≤ secondDiff q₁ D := by
  -- G(r) = C'(r+D) + C'(r−D) − 2C'(r) ≥ 0 on [0, q₁]
  have hG : ∀ r ∈ Icc 0 q₁, 0 ≤ Cd (r + D) + Cd (r - D) - 2 * Cd r := by
    have hmono : MonotoneOn (fun r => Cd (r + D) + Cd (r - D) - 2 * Cd r) (Icc 0 q₁) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 q₁)
        (f' := fun r => (phiC (r + D) + phiC (r - D) - 2 * phiC r) / Real.log 2)
      · intro r hr
        have d1 := (hasDerivAt_Cd (by linarith [hr.1]) (by linarith [hr.2])).comp r
          ((hasDerivAt_id' r).add_const D)
        have d2 := (hasDerivAt_Cd (by linarith [hr.1]) (by linarith [hr.2])).comp r
          ((hasDerivAt_id' r).sub_const D)
        have d3 := hasDerivAt_Cd (r := r) (by linarith [hr.1]) (by linarith [hr.2])
        exact ((d1.continuousAt.add d2.continuousAt).sub
          (continuousAt_const.mul d3.continuousAt)).continuousWithinAt
      · intro r hr
        rw [interior_Icc] at hr
        have d1 := (hasDerivAt_Cd (by linarith [hr.1]) (by linarith [hr.2])).comp r
          ((hasDerivAt_id' r).add_const D)
        have d2 := (hasDerivAt_Cd (by linarith [hr.1]) (by linarith [hr.2])).comp r
          ((hasDerivAt_id' r).sub_const D)
        have d3 := hasDerivAt_Cd (r := r) (by linarith [hr.1]) (by linarith [hr.2])
        have hd := (d1.add d2).sub (d3.const_mul 2)
        have hval : phiC (r + D) / Real.log 2 * 1 + phiC (r - D) / Real.log 2 * 1 -
            2 * (phiC r / Real.log 2) = (phiC (r + D) + phiC (r - D) - 2 * phiC r) / Real.log 2 := by
          ring
        rw [hval] at hd
        exact hd.hasDerivWithinAt
      · intro r hr
        rw [interior_Icc] at hr
        have hm := phiC_sym_mono (q := r) (D := D) (s := 0) (t := D) (by linarith [hr.2])
          (by linarith [hr.1]) le_rfl hD le_rfl
        simp only [add_zero, sub_zero] at hm
        apply div_nonneg _ log_two_pos.le
        linarith
    intro r hr
    have h0 : Cd (0 + D) + Cd (0 - D) - 2 * Cd 0 = 0 := by
      rw [zero_add, zero_sub, Cd_neg]
      simp [Cd]
    have := hmono ⟨le_rfl, hq.trans hqq⟩ hr hr.1
    simp only at this
    linarith
  -- g(r) = h_r(D) is monotone on [0, q₁]
  have hgmono : MonotoneOn (fun r => secondDiff r D) (Icc 0 q₁) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 q₁)
      (f' := fun r => Cd (r + D) + Cd (r - D) - 2 * Cd r)
    · intro r hr
      have d1 := (hasDerivAt_Cf (by linarith [hr.1]) (by linarith [hr.2])).comp r
        ((hasDerivAt_id' r).add_const D)
      have d2 := (hasDerivAt_Cf (by linarith [hr.1]) (by linarith [hr.2])).comp r
        ((hasDerivAt_id' r).sub_const D)
      have d3 := hasDerivAt_Cf (r := r) (by linarith [hr.1]) (by linarith [hr.2])
      exact ((d1.continuousAt.add d2.continuousAt).sub
        (continuousAt_const.mul d3.continuousAt)).continuousWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      have d1 := (hasDerivAt_Cf (by linarith [hr.1]) (by linarith [hr.2])).comp r
        ((hasDerivAt_id' r).add_const D)
      have d2 := (hasDerivAt_Cf (by linarith [hr.1]) (by linarith [hr.2])).comp r
        ((hasDerivAt_id' r).sub_const D)
      have d3 := hasDerivAt_Cf (r := r) (by linarith [hr.1]) (by linarith [hr.2])
      have hd := (d1.add d2).sub (d3.const_mul 2)
      have hval : Cd (r + D) * 1 + Cd (r - D) * 1 - 2 * Cd r = Cd (r + D) + Cd (r - D) - 2 * Cd r := by
        ring
      rw [hval] at hd
      exact hd.hasDerivWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact hG r ⟨hr.1.le, hr.2.le⟩
  exact hgmono ⟨hq, hqq⟩ ⟨hq.trans hqq, le_rfl⟩ hqq

/-- `Δ` of a canonical law equals `secondDiff q d / 2`. -/
theorem entropyDrop_eq_secondDiff {a b : ℝ} :
    H ((a + b) / 2) - (H a + H b) / 2 = secondDiff (1 - a - b) (b - a) / 2 := by
  unfold secondDiff Cf
  have e1 : (1 - (1 - a - b + (b - a))) / 2 = a := by ring
  have e2 : (1 - (1 - a - b - (b - a))) / 2 = b := by ring
  have e3 : (1 - (1 - a - b)) / 2 = (a + b) / 2 := by ring
  rw [e1, e2, e3]
  ring

end CKLaneN1

end


