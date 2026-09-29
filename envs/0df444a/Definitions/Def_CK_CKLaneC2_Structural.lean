-- Prove2me | Definitions.Def_CK_CKLaneC2_Structural
-- name    : CK_CKLaneC2_Structural
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T08:04:28.227644+00:00
-- url     : https://prove2.me/theorems/842bb6d3-32fc-426f-a799-ce4d702f7ebf
-- title:
--   Courtade–Kumar proof module `CKLaneC2.Structural` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC2.Structural` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC2.Structural` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC2.Structural (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC2/Structural.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8Inverse
import Definitions.Def_CK_GeneralCK_PureGapHalfMeanAnalytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

-- ===== source module CKLaneC2.Structural =====
section
/-
Lane C2 — THE ARCTAN COMPARISON (structural lemma).

Write `r(t) = 1/Θ'(t)`, `r0 = 1/θ0 = log 2 / 8` and `gfun t = (r(t) - r0)/t^2`, so that
`Θ'(t) = 1/(r0 + gfun t · t^2)`.  For a profile with CONSTANT `gfun ≡ β` (an arctan profile,
`Θ = arctan(k t)/(r0 k)`, `r0 k^2 = β`) the half-mean slope gap is an exact EQUALITY:
the doubling point of `x` is exactly `K x = 2x/(1 - β x^2/r0) = 2Θ'(x)x/(2Θ'(x) - θ0)`.

`slope_gap_of_comparison`: if `gfun` is ANTITONE on `[x₁, T]`, `gfun T > 0`, and one point condition
holds at `x₁` (`Θ(x₁) < θ0 x₁ p(U)` with `U ≥ gfun x₁ · x₁^2 / r0`, `p(s) = 1 - s/3 + s^2/5 - s^3/7`),
then for every `x₁ ≤ x < w ≤ T` with `Θ(w) = 2Θ(x)` and `θ0 < 2Θ'(x)`:
    `w (2Θ'(x) - θ0) < 2Θ'(x) x`.
Proof: compare `Θ` with the arctan profile of slope `β = gfun x` below `x` (Θ' ≤ Ψ') and above `x`
(Θ' ≥ Ψ'), then use `arctan a + arctan a = arctan (2a/(1-a^2))`.  No numerics here.
-/

set_option autoImplicit false

namespace CKLaneC2

open GeneralCK Set

noncomputable def r0 : ℝ := Real.log 2 / 8

theorem r0_pos : 0 < r0 := by
  unfold r0
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  positivity

theorem theta0_eq : pureGapTheta0 = 1 / r0 := by
  have h : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold pureGapTheta0 r0
  field_simp

/-- The arctan-comparison slope. -/
noncomputable def gfun (t : ℝ) : ℝ := (1 / deriv e8Theta t - r0) / t ^ 2

theorem deriv_eq_gfun {t : ℝ} (ht : 0 < t) : deriv e8Theta t = 1 / (r0 + gfun t * t ^ 2) := by
  have hd := deriv_e8Theta_pos ht
  have ht2 : t ^ 2 ≠ 0 := by positivity
  unfold gfun
  rw [div_mul_cancel₀ _ ht2]
  have e : r0 + (1 / deriv e8Theta t - r0) = 1 / deriv e8Theta t := by ring
  rw [e, one_div_one_div]

/-- `p(s) = 1 - s/3 + s^2/5 - s^3/7`. -/
noncomputable def ppoly (s : ℝ) : ℝ := 1 - s / 3 + s ^ 2 / 5 - s ^ 3 / 7

theorem ppoly_anti {s s' : ℝ} (hss' : s ≤ s') : ppoly s' ≤ ppoly s := by
  have hQ : 0 ≤ 1 / 3 - (s + s') / 5 + (s ^ 2 + s * s' + s' ^ 2) / 7 := by
    nlinarith [sq_nonneg (s + s' - 14 / 15), sq_nonneg (s - s')]
  have e : ppoly s - ppoly s' = (s' - s) * (1 / 3 - (s + s') / 5 + (s ^ 2 + s * s' + s' ^ 2) / 7) := by
    unfold ppoly; ring
  have := mul_nonneg (sub_nonneg.mpr hss') hQ
  linarith

theorem arctan_ge_poly {u : ℝ} (hu : 0 ≤ u) : u * ppoly (u ^ 2) ≤ Real.arctan u := by
  have hmono : MonotoneOn (fun v : ℝ => Real.arctan v - (v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7)) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun v => v ^ 8 / (1 + v ^ 2))
    · exact (Real.continuous_arctan.sub (by fun_prop)).continuousOn
    · intro v _
      have h1 := Real.hasDerivAt_arctan v
      have h2 : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3 + v ^ 5 / 5 - v ^ 7 / 7)
          (1 - v ^ 2 + v ^ 4 - v ^ 6) v := by
        have h := ((((hasDerivAt_id' (x := v)).sub ((hasDerivAt_pow 3 v).div_const 3)).add
          ((hasDerivAt_pow 5 v).div_const 5)).sub ((hasDerivAt_pow 7 v).div_const 7))
        refine h.congr_deriv ?_
        push_cast
        ring
      have h3 := h1.sub h2
      refine (h3.congr_deriv ?_).hasDerivWithinAt
      have hpos : (0 : ℝ) < 1 + v ^ 2 := by positivity
      field_simp
      ring
    · intro v _
      positivity
  have h := hmono (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hu) hu
  simp only [Real.arctan_zero] at h
  unfold ppoly
  nlinarith [h]

/-- The comparison profile `Ψ_k(t) = arctan(k t)/(r0 k)`, with `Ψ_k' = 1/(r0 + r0 k^2 t^2)`. -/
noncomputable def Psi (k t : ℝ) : ℝ := Real.arctan (k * t) / (r0 * k)

theorem hasDerivAt_Psi {k : ℝ} (hk : 0 < k) (t : ℝ) :
    HasDerivAt (Psi k) (1 / (r0 + r0 * k ^ 2 * t ^ 2)) t := by
  have hr := r0_pos
  have h1 : HasDerivAt (fun t : ℝ => k * t) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have h2 := ((Real.hasDerivAt_arctan (k * t)).comp t h1).div_const (r0 * k)
  refine h2.congr_deriv ?_
  have hpos : (0 : ℝ) < 1 + (k * t) ^ 2 := by positivity
  have hpos2 : (0 : ℝ) < r0 + r0 * k ^ 2 * t ^ 2 := by positivity
  field_simp

/-- **THE STRUCTURAL LEMMA.** -/
theorem slope_gap_of_comparison
    {x₁ T : ℝ} (hx₁ : 0 < x₁)
    (hanti : AntitoneOn gfun (Icc x₁ T))
    (hgT : 0 < gfun T)
    {U : ℝ} (hU : gfun x₁ * x₁ ^ 2 / r0 ≤ U)
    (hS2 : e8Theta x₁ < pureGapTheta0 * x₁ * ppoly U)
    {x w : ℝ} (hx : x₁ ≤ x) (hxw : x < w) (hwT : w ≤ T)
    (hcouple : e8Theta w = 2 * e8Theta x)
    (hlarge : pureGapTheta0 < 2 * deriv e8Theta x) :
    w * (2 * deriv e8Theta x - pureGapTheta0) < 2 * deriv e8Theta x * x := by
  have hx0 : 0 < x := lt_of_lt_of_le hx₁ hx
  have hw0 : 0 < w := by linarith
  have hxT : x ≤ T := by linarith
  have hr0 := r0_pos
  have hr0ne : r0 ≠ 0 := hr0.ne'
  have hTmem : T ∈ Icc x₁ T := ⟨by linarith, le_refl T⟩
  have hgpos : ∀ t, x₁ ≤ t → t ≤ T → 0 < gfun t := fun t h1 h2 =>
    lt_of_lt_of_le hgT (hanti ⟨h1, h2⟩ hTmem h2)
  have hderiv : ∀ t, 0 < t → deriv e8Theta t = 1 / (r0 + gfun t * t ^ 2) :=
    fun t ht => deriv_eq_gfun ht
  have hThetaD : ∀ t, 0 < t → HasDerivAt e8Theta (deriv e8Theta t) t :=
    fun t ht => (hasDerivAt_e8Theta ht).differentiableAt.hasDerivAt
  set β := gfun x with hβ
  have hβpos : 0 < β := hgpos x hx hxT
  set k := Real.sqrt (β / r0) with hk
  have hkpos : 0 < k := Real.sqrt_pos.mpr (div_pos hβpos hr0)
  have hk2 : r0 * k ^ 2 = β := by
    rw [hk, Real.sq_sqrt (div_pos hβpos hr0).le]
    field_simp
  -- Step A: Ψ - Θ is monotone on [x₁, x]
  have hA : MonotoneOn (fun t => Psi k t - e8Theta t) (Icc x₁ x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x₁ x)
      (f' := fun t => 1 / (r0 + r0 * k ^ 2 * t ^ 2) - deriv e8Theta t)
    · intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hx₁ ht.1
      exact ((hasDerivAt_Psi hkpos t).sub (hThetaD t htpos)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htpos : 0 < t := lt_trans hx₁ ht.1
      exact ((hasDerivAt_Psi hkpos t).sub (hThetaD t htpos)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htpos : 0 < t := lt_trans hx₁ ht.1
      have hgt : β ≤ gfun t := hanti ⟨ht.1.le, by linarith [ht.2]⟩ ⟨hx, hxT⟩ ht.2.le
      rw [hderiv t htpos, hk2]
      have h1 : 0 < r0 + β * t ^ 2 := by positivity
      have h2 : r0 + β * t ^ 2 ≤ r0 + gfun t * t ^ 2 := by nlinarith [sq_nonneg t]
      have := one_div_le_one_div_of_le h1 h2
      linarith
  -- Step B: Θ(x₁) < Ψ(x₁)
  have hB : e8Theta x₁ < Psi k x₁ := by
    have hu : 0 ≤ k * x₁ := by positivity
    have harc := arctan_ge_poly hu
    have hg1 : β ≤ gfun x₁ := hanti ⟨le_refl _, by linarith⟩ ⟨hx, hxT⟩ hx
    have hu2 : (k * x₁) ^ 2 ≤ U := by
      have e : (k * x₁) ^ 2 = β * x₁ ^ 2 / r0 := by
        rw [← hk2]; field_simp
      rw [e]
      calc β * x₁ ^ 2 / r0 ≤ gfun x₁ * x₁ ^ 2 / r0 := by gcongr
        _ ≤ U := hU
    have hp := ppoly_anti hu2
    rw [theta0_eq] at hS2
    unfold Psi
    rw [lt_div_iff₀ (by positivity)]
    calc e8Theta x₁ * (r0 * k) < (1 / r0 * x₁ * ppoly U) * (r0 * k) :=
          mul_lt_mul_of_pos_right hS2 (by positivity)
      _ = k * x₁ * ppoly U := by field_simp
      _ ≤ k * x₁ * ppoly ((k * x₁) ^ 2) := mul_le_mul_of_nonneg_left hp hu
      _ ≤ Real.arctan (k * x₁) := harc
  -- Step C
  have hC : e8Theta x < Psi k x := by
    have h := hA ⟨le_refl x₁, hx⟩ ⟨hx, le_refl x⟩ hx
    simp only at h
    linarith
  -- Step D: Θ - Ψ is monotone on [x, w]
  have hD : MonotoneOn (fun t => e8Theta t - Psi k t) (Icc x w) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc x w)
      (f' := fun t => deriv e8Theta t - 1 / (r0 + r0 * k ^ 2 * t ^ 2))
    · intro t ht
      have htpos : 0 < t := lt_of_lt_of_le hx0 ht.1
      exact ((hThetaD t htpos).sub (hasDerivAt_Psi hkpos t)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htpos : 0 < t := lt_trans hx0 ht.1
      exact ((hThetaD t htpos).sub (hasDerivAt_Psi hkpos t)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have htpos : 0 < t := lt_trans hx0 ht.1
      have ht1 : x₁ ≤ t := by linarith [ht.1]
      have ht2 : t ≤ T := by linarith [ht.2]
      have hgt : gfun t ≤ β := hanti ⟨hx, hxT⟩ ⟨ht1, ht2⟩ ht.1.le
      have hgtpos := hgpos t ht1 ht2
      rw [hderiv t htpos, hk2]
      have h1 : 0 < r0 + gfun t * t ^ 2 := by positivity
      have h2 : r0 + gfun t * t ^ 2 ≤ r0 + β * t ^ 2 := by nlinarith [sq_nonneg t]
      have := one_div_le_one_div_of_le h1 h2
      linarith
  have hE := hD ⟨le_refl x, hxw.le⟩ ⟨hxw.le, le_refl w⟩ hxw.le
  simp only at hE
  have hPsiw : Psi k w < 2 * Psi k x := by linarith
  -- Step F: k x < 1 from the large-derivative case
  have hDx : 0 < r0 + β * x ^ 2 := by positivity
  have hkx2 : (k * x) ^ 2 < 1 := by
    have h1 : pureGapTheta0 < 2 * (1 / (r0 + β * x ^ 2)) := by
      rw [← hderiv x hx0]; exact hlarge
    rw [theta0_eq] at h1
    have h2 := mul_lt_mul_of_pos_right h1 (show 0 < r0 * (r0 + β * x ^ 2) by positivity)
    have e1 : 1 / r0 * (r0 * (r0 + β * x ^ 2)) = r0 + β * x ^ 2 := by field_simp
    have e2 : 2 * (1 / (r0 + β * x ^ 2)) * (r0 * (r0 + β * x ^ 2)) = 2 * r0 := by field_simp
    rw [e1, e2] at h2
    have e3 : (k * x) ^ 2 = β * x ^ 2 / r0 := by rw [← hk2]; field_simp
    rw [e3, div_lt_one hr0]
    linarith
  have harc : Real.arctan (k * w) < Real.arctan (2 * (k * x) / (1 - (k * x) ^ 2)) := by
    have h := mul_lt_mul_of_pos_right hPsiw (show 0 < r0 * k by positivity)
    have e1 : Psi k w * (r0 * k) = Real.arctan (k * w) := by
      unfold Psi; field_simp
    have e2 : 2 * Psi k x * (r0 * k) = 2 * Real.arctan (k * x) := by
      unfold Psi; field_simp
    rw [e1, e2] at h
    have hadd := Real.arctan_add (x := k * x) (y := k * x) (by nlinarith)
    have e3 : 2 * (k * x) / (1 - (k * x) ^ 2) = (k * x + k * x) / (1 - k * x * (k * x)) := by ring
    rw [e3, ← hadd]
    linarith
  have hkw : k * w < 2 * (k * x) / (1 - (k * x) ^ 2) := Real.arctan_strictMono.lt_iff_lt.mp harc
  have h1mk : 0 < 1 - (k * x) ^ 2 := by linarith
  have key : w * (1 - (k * x) ^ 2) < 2 * x := by
    have h := (lt_div_iff₀ h1mk).mp hkw
    nlinarith
  rw [hderiv x hx0, theta0_eq]
  have e1 : w * (2 * (1 / (r0 + β * x ^ 2)) - 1 / r0) = w * (1 - (k * x) ^ 2) / (r0 + β * x ^ 2) := by
    rw [← hk2]; field_simp; ring
  have e2 : 2 * (1 / (r0 + β * x ^ 2)) * x = 2 * x / (r0 + β * x ^ 2) := by field_simp
  rw [e1, e2, div_lt_div_iff₀ hDx hDx]
  exact mul_lt_mul_of_pos_right key hDx

end CKLaneC2

end


