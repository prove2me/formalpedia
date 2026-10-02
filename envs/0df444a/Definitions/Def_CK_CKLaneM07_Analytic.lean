-- Prove2me | Definitions.Def_CK_CKLaneM07_Analytic
-- name    : CK_CKLaneM07_Analytic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T17:23:18.683971+00:00
-- url     : https://prove2.me/theorems/cdcc8e02-b882-4e3a-a3dc-4deb11c0c9cf
-- title:
--   Courtade–Kumar proof module `CKLaneM07.Analytic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.Analytic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.Analytic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.Analytic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/Analytic.lean)

import Definitions.Def_CK_CKLaneE_FastPoint
import Definitions.Def_CK_CKLaneE_EntropyDropSharp
import Definitions.Def_CK_CKLaneE_NLSChecker
import Definitions.Def_CK_GeneralCK_PsiLogSumOwner
import Definitions.Def_CK_GeneralCK_PureGapCapZeroReduction
import Definitions.Def_CK_GeneralCK_ScalarGap
import Definitions.Def_CK_GeneralCK_PhysicalSlope
import Definitions.Def_CK_GeneralCK_DeterministicCap
import Definitions.Def_CK_GeneralCK_FCAnalytic

-- ===== source module CKLaneM07.Analytic =====
section

/-!
# Lane M07: analytic layer for the archived same-side `derivative` method

Archive criterion (`same_side/COVER.py`, owner `derivative`):
`beta_lo ≥ K · P''(I_hi)`, i.e. along the entropy-deficit direction the function
`G(s) = j + β d² s - P(Δ+s) + P(s)` has nonnegative derivative, and `G(0) ≥ 0`.

This module proves, with no numerical input:
* `crR_mono`: the normalized bias deficit `C(z)/z²`, `C(z) = 1 - H((1-z)/2)`, is nondecreasing
  on `(0,1)` (derivative `g(z)/z³ ≥ 0`, `g` from `CKLaneE.g_ge_quartic`);
* `entropyDrop_eq_cr`: `Δ = d²·(C(ρ)/ρ²/(4m) + C(κ)/κ²/(4(1-m)))`, `ρ = d/(a+b)`, `κ = d/(2-a-b)`;
* `crR_le_poly`: `C(z)/z² ≤ (1 + zh²/6 + 2zh⁴/5)/(2 L0)` for `z ≤ zh`, `L0 ≤ log 2`;
* `etaCurvature_H`, `etaCurvature_le_anchor`: closed form of `P''` at an anchor `1 - H v` and
  monotone transfer (`P'' = etaCurvature (1 - ·)` is nondecreasing);
* `derivative_criterion`: if `P Δ ≤ j` and `Δ · P''(y) ≤ α` for all `0 < y ≤ Δ + s`, then
  `P(Δ+s) - P(s) ≤ j + α s` (monotonicity of `G` from `HasDerivAt`, slope of the convex `P1`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CKLaneM07

open GeneralCK GeneralCK.Scalar Set

/-! ## 1. The normalized bias deficit `C(z)/z²` is nondecreasing -/

/-- `Fb z = (1+z) log(1+z) + (1-z) log(1-z) = 2 log 2 · (1 - H((1-z)/2))`. -/
noncomputable def Fb (z : ℝ) : ℝ := (1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)

theorem hasDerivAt_Fb {z : ℝ} (hz0 : -1 < z) (hz1 : z < 1) :
    HasDerivAt Fb (Real.log (1 + z) - Real.log (1 - z)) z := by
  have h1 : (1 + z) ≠ 0 := by intro h; linarith
  have h2 : (1 - z) ≠ 0 := by intro h; linarith
  have hA := ((hasDerivAt_id' z).const_add 1).mul (((hasDerivAt_id' z).const_add 1).log h1)
  have hB := ((hasDerivAt_id' z).const_sub 1).mul (((hasDerivAt_id' z).const_sub 1).log h2)
  have hd := hA.add hB
  show HasDerivAt (fun z => (1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)) _ z
  refine hd.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_Fbq {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z : ℝ => Fb z / z ^ 2)
      ((-(2 + z) * Real.log (1 + z) - (2 - z) * Real.log (1 - z)) / z ^ 3) z := by
  have hz0 : 0 < z := hz.1
  have hF := hasDerivAt_Fb (by linarith [hz.1]) hz.2
  have hq := hF.div (hasDerivAt_pow 2 z) (by positivity : z ^ 2 ≠ 0)
  refine hq.congr_deriv ?_
  simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]
  unfold Fb
  field_simp
  ring

theorem Fbq_monotoneOn : MonotoneOn (fun z : ℝ => Fb z / z ^ 2) (Ioo 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo 0 1)
    (f' := fun z => (-(2 + z) * Real.log (1 + z) - (2 - z) * Real.log (1 - z)) / z ^ 3)
  · intro z hz
    exact (hasDerivAt_Fbq hz).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioo] at hz
    exact (hasDerivAt_Fbq hz).hasDerivWithinAt
  · intro z hz
    rw [interior_Ioo] at hz
    have hg := CKLaneE.g_ge_quartic hz.1.le hz.2
    have h4 : (0 : ℝ) ≤ z ^ 4 / 3 := by positivity
    have hn : 0 ≤ -(2 + z) * Real.log (1 + z) - (2 - z) * Real.log (1 - z) := h4.trans hg
    exact div_nonneg hn (pow_pos hz.1 3).le

/-- Normalized bias deficit `C(z)/z²`. -/
noncomputable def crR (z : ℝ) : ℝ := (1 - H ((1 - z) / 2)) / z ^ 2

theorem crR_eq {z : ℝ} (hz0 : -1 < z) (hz1 : z < 1) :
    crR z = (Fb z / z ^ 2) / (2 * Real.log 2) := by
  unfold crR
  rw [CKLaneE.biasDeficit_eq_logs hz1 hz0]
  unfold Fb
  ring

/-- `C(z)/z²` is nondecreasing on `(0,1)`. -/
theorem crR_mono {z z' : ℝ} (hz : 0 < z) (hzz : z ≤ z') (hz' : z' < 1) : crR z ≤ crR z' := by
  have hm := Fbq_monotoneOn ⟨hz, lt_of_le_of_lt hzz hz'⟩ ⟨lt_of_lt_of_le hz hzz, hz'⟩ hzz
  simp only at hm
  rw [crR_eq (by linarith) (by linarith), crR_eq (by linarith) hz']
  exact div_le_div_of_nonneg_right hm (by positivity)

theorem crR_nonneg (z : ℝ) : 0 ≤ crR z := by
  unfold crR
  have h := H_le_one ((1 - z) / 2)
  exact div_nonneg (by linarith) (sq_nonneg z)

/-- Exact normalized form of the entropy drop. -/
theorem entropyDrop_eq_cr {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 =
      (b - a) ^ 2 * (crR ((b - a) / (a + b)) / (4 * ((a + b) / 2)) +
        crR ((b - a) / (2 - a - b)) / (4 * (1 - (a + b) / 2))) := by
  have hchain := deterministic_entropy_chain ha (hab.trans hb) (ha.trans hab) hb
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hd : 0 < b - a := by linarith
  have hpa : a / (a + b) = (1 - (b - a) / (a + b)) / 2 := by field_simp; ring
  have hpb : (1 - b) / (2 - a - b) = (1 - (b - a) / (2 - a - b)) / 2 := by field_simp; ring
  rw [hchain, hpa, hpb]
  unfold crR
  generalize H ((1 - (b - a) / (a + b)) / 2) = A
  generalize H ((1 - (b - a) / (2 - a - b)) / 2) = B
  have hs' : a + b ≠ 0 := hs.ne'
  have ht' : 2 - a - b ≠ 0 := ht.ne'
  have hd' : b - a ≠ 0 := hd.ne'
  have ht'' : 2 - (a + b) ≠ 0 := by intro h; linarith
  field_simp
  ring

/-- Polynomial upper bound for `C(z)/z²`, monotone in the upper endpoint `zh`. -/
theorem crR_le_poly {z zh L0 : ℝ} (hz : 0 < z) (hzz : z ≤ zh) (hz1 : z < 1) (hL0 : 0 < L0)
    (hL0' : L0 ≤ Real.log 2) :
    crR z ≤ (1 + zh ^ 2 / 6 + 2 / 5 * zh ^ 4) / (2 * L0) := by
  have hp := CKLaneE.biasDeficit_le_poly6 hz.le hz1
  have hz2 : 0 < z ^ 2 := by positivity
  unfold crR
  rw [div_le_iff₀ hz2]
  have hzh2 : z ^ 2 ≤ zh ^ 2 := pow_le_pow_left₀ hz.le hzz 2
  have hzh4 : z ^ 4 ≤ zh ^ 4 := pow_le_pow_left₀ hz.le hzz 4
  have hnum : 1 + z ^ 2 / 6 + 2 / 5 * z ^ 4 ≤ 1 + zh ^ 2 / 6 + 2 / 5 * zh ^ 4 := by linarith
  have hpos : 0 ≤ 1 + zh ^ 2 / 6 + 2 / 5 * zh ^ 4 := by positivity
  calc 1 - H ((1 - z) / 2) ≤ (z ^ 2 + z ^ 4 / 6 + 2 / 5 * z ^ 6) / (2 * Real.log 2) := hp
    _ = (1 + z ^ 2 / 6 + 2 / 5 * z ^ 4) / (2 * Real.log 2) * z ^ 2 := by ring
    _ ≤ (1 + zh ^ 2 / 6 + 2 / 5 * zh ^ 4) / (2 * L0) * z ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hz2.le
        exact div_le_div₀ hpos hnum (by positivity) (by linarith)

/-- Entropy drop bound from upper bounds of the two normalized bias deficits. -/
theorem entropyDrop_le_K {a b U1 U2 mL mH : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (hU1 : crR ((b - a) / (a + b)) ≤ U1) (hU2 : crR ((b - a) / (2 - a - b)) ≤ U2)
    (hmL : 0 < mL) (hmL' : mL ≤ (a + b) / 2) (hmH : (a + b) / 2 ≤ mH) (hmH1 : mH < 1) :
    H ((a + b) / 2) - (H a + H b) / 2 ≤ (b - a) ^ 2 * (U1 / (4 * mL) + U2 / (4 * (1 - mH))) := by
  rw [entropyDrop_eq_cr ha hab hb]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hs : 0 < a + b := by linarith
  have ht : 0 < 2 - a - b := by linarith
  have hU1n : 0 ≤ U1 := (crR_nonneg _).trans hU1
  have hU2n : 0 ≤ U2 := (crR_nonneg _).trans hU2
  apply add_le_add
  · calc crR ((b - a) / (a + b)) / (4 * ((a + b) / 2)) ≤ U1 / (4 * ((a + b) / 2)) :=
          div_le_div_of_nonneg_right hU1 (by positivity)
      _ ≤ U1 / (4 * mL) := div_le_div_of_nonneg_left hU1n (by positivity) (by linarith)
  · calc crR ((b - a) / (2 - a - b)) / (4 * (1 - (a + b) / 2)) ≤ U2 / (4 * (1 - (a + b) / 2)) :=
          div_le_div_of_nonneg_right hU2 (by linarith)
      _ ≤ U2 / (4 * (1 - mH)) := div_le_div_of_nonneg_left hU2n (by linarith) (by linarith)

/-! ## 2. Curvature `P'' = etaCurvature (1 - ·)` at an anchor -/

/-- Closed form of `etaCurvature (H v)` for `0 < v < 1/2`. -/
theorem etaCurvature_H {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    etaCurvature (H v) =
      Real.log 2 * ((v ^ 2 + (1 - v) ^ 2) * Real.log ((1 - v) / v) - (1 - 2 * v)) /
        (v ^ 2 * (1 - v) ^ 2 * Real.log ((1 - v) / v) ^ 3) := by
  have hH0 : 0 < H v := H_pos hv (by linarith)
  have hH1 : H v < 1 := CKLaneE.H_lt_one_of_lt_half hv.le hv'
  rw [FCAnalytic.etaCurvature_form hH0 hH1, entropyInverse_H_lower hv.le hv'.le]

/-- `P''(y) = etaCurvature (1 - y)` is at most its value at the anchor `1 - H v` when
`y ≤ 1 - H v`. -/
theorem etaCurvature_le_anchor {v y : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) (hy0 : 0 < y)
    (hy1 : y < 1) (hHy : H v ≤ 1 - y) :
    etaCurvature (1 - y) ≤ etaCurvature (H v) := by
  have hH0 : 0 < H v := H_pos hv (by linarith)
  have hH1 : H v < 1 := CKLaneE.H_lt_one_of_lt_half hv.le hv'
  exact etaCurvature_antitoneOn ⟨hH0, hH1⟩ ⟨by linarith, by linarith⟩ hHy

/-- The curvature numerator at an anchor is nonnegative. -/
theorem anchor_numerator_nonneg {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    0 ≤ (v ^ 2 + (1 - v) ^ 2) * Real.log ((1 - v) / v) - (1 - 2 * v) := by
  have h := curvatureNumerator_nonneg hv hv'.le
  unfold curvatureNumerator J at h
  have hL : Real.log 2 ≠ 0 := log_two_pos.ne'
  have e : (v ^ 2 + (1 - v) ^ 2) * Real.log 2 * (Real.log ((1 - v) / v) / Real.log 2) =
      (v ^ 2 + (1 - v) ^ 2) * Real.log ((1 - v) / v) := by field_simp
  rw [e] at h
  exact h

/-- Rational-friendly upper bound of `etaCurvature (H v)` from enclosures of `log 2` and of
`ℓ = log((1-v)/v)`. -/
theorem etaCurvature_H_le {v Lh ℓlo ℓhi : ℝ} (hv : 0 < v) (hv' : v < 1 / 2)
    (hL : Real.log 2 ≤ Lh) (hlo : ℓlo ≤ Real.log ((1 - v) / v))
    (hhi : Real.log ((1 - v) / v) ≤ ℓhi) (hlo0 : 0 < ℓlo) :
    etaCurvature (H v) ≤
      Lh * ((v * v + (1 - v) * (1 - v)) * ℓhi - (1 - 2 * v)) /
        (v * v * ((1 - v) * (1 - v)) * (ℓlo * ℓlo * ℓlo)) := by
  rw [etaCurvature_H hv hv']
  set ℓ := Real.log ((1 - v) / v) with hℓ
  have hN := anchor_numerator_nonneg hv hv'
  rw [← hℓ] at hN
  have hv1 : 0 < 1 - v := by linarith
  have hvv : 0 < v * v * ((1 - v) * (1 - v)) := mul_pos (mul_pos hv hv) (mul_pos hv1 hv1)
  have hq : 0 ≤ v * v + (1 - v) * (1 - v) := by positivity
  have hNle : (v ^ 2 + (1 - v) ^ 2) * ℓ - (1 - 2 * v) ≤
      (v * v + (1 - v) * (1 - v)) * ℓhi - (1 - 2 * v) := by
    have := mul_le_mul_of_nonneg_left hhi hq
    nlinarith
  have hLpos : 0 < Real.log 2 := log_two_pos
  have hnum : Real.log 2 * ((v ^ 2 + (1 - v) ^ 2) * ℓ - (1 - 2 * v)) ≤
      Lh * ((v * v + (1 - v) * (1 - v)) * ℓhi - (1 - 2 * v)) :=
    mul_le_mul hL hNle hN (hLpos.le.trans hL)
  have hℓpos : 0 < ℓ := lt_of_lt_of_le hlo0 hlo
  have hcube : ℓlo * ℓlo * ℓlo ≤ ℓ ^ 3 := by
    have h1 : ℓlo * ℓlo ≤ ℓ * ℓ := mul_le_mul hlo hlo hlo0.le hℓpos.le
    have h2 : ℓlo * ℓlo * ℓlo ≤ ℓ * ℓ * ℓ := mul_le_mul h1 hlo hlo0.le (by positivity)
    calc ℓlo * ℓlo * ℓlo ≤ ℓ * ℓ * ℓ := h2
      _ = ℓ ^ 3 := by ring
  have hden : v * v * ((1 - v) * (1 - v)) * (ℓlo * ℓlo * ℓlo) ≤ v ^ 2 * (1 - v) ^ 2 * ℓ ^ 3 := by
    have e : v ^ 2 * (1 - v) ^ 2 * ℓ ^ 3 = v * v * ((1 - v) * (1 - v)) * ℓ ^ 3 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hcube hvv.le
  have hdenpos : 0 < v * v * ((1 - v) * (1 - v)) * (ℓlo * ℓlo * ℓlo) :=
    mul_pos hvv (mul_pos (mul_pos hlo0 hlo0) hlo0)
  have hnumpos : 0 ≤ Lh * ((v * v + (1 - v) * (1 - v)) * ℓhi - (1 - 2 * v)) :=
    (mul_nonneg hLpos.le hN).trans hnum
  exact div_le_div₀ hnumpos hnum hdenpos hden

/-! ## 3. The derivative criterion -/

/-- **Derivative criterion.**  `G(σ) = j + α σ - P(Δ+σ) + P(σ)` has `G(0) = j - P Δ ≥ 0` and
`G'(σ) = α - (P1(Δ+σ) - P1 σ) ≥ α - Δ · P''(Δ+σ) ≥ 0` on `(0, s)`; hence `G(s) ≥ 0`. -/
theorem derivative_criterion {j α Δ s : ℝ} (hΔ : 0 ≤ Δ) (hs : 0 ≤ s) (hcap : Δ + s < 1)
    (hzero : P Δ ≤ j)
    (hcurv : ∀ y : ℝ, 0 < y → y ≤ Δ + s → Δ * etaCurvature (1 - y) ≤ α) :
    P (Δ + s) - P s ≤ j + α * s := by
  let G : ℝ → ℝ := fun σ => j + α * σ - P (Δ + σ) + P σ
  have hcont : ContinuousOn G (Icc 0 s) := by
    have hleft : ContinuousOn (fun σ => P (Δ + σ)) (Icc 0 s) := by
      apply P_continuousOn.comp (continuous_const.add continuous_id).continuousOn
      intro σ hσ
      change 0 ≤ Δ + σ ∧ Δ + σ < 1
      exact ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
    have hright : ContinuousOn P (Icc 0 s) :=
      P_continuousOn.mono (fun σ hσ => ⟨hσ.1, by linarith [hσ.2]⟩)
    exact ((continuous_const.add (continuous_const.mul continuous_id)).continuousOn.sub
      hleft).add hright
  have hderiv : ∀ σ ∈ interior (Icc 0 s),
      HasDerivWithinAt G (α - P1 (Δ + σ) + P1 σ) (interior (Icc 0 s)) σ := by
    intro σ hσ
    rw [interior_Icc] at hσ
    have h1 : 0 < Δ + σ := by linarith [hσ.1]
    have h2 : Δ + σ < 1 := by linarith [hσ.2]
    have hPa := CKLaneE.hasDerivAt_P_P1 h1 h2
    have hPb := CKLaneE.hasDerivAt_P_P1 hσ.1 (by linarith [hσ.2])
    have hd := ((((hasDerivAt_id σ).const_mul α).const_add j).sub
      (hPa.comp σ ((hasDerivAt_id σ).const_add Δ))).add hPb
    exact (hd.congr_deriv (by simp)).hasDerivWithinAt
  have hnonneg : ∀ σ ∈ interior (Icc 0 s), 0 ≤ α - P1 (Δ + σ) + P1 σ := by
    intro σ hσ
    rw [interior_Icc] at hσ
    have hy0 : 0 < Δ + σ := by linarith [hσ.1]
    have hy1 : Δ + σ < 1 := by linarith [hσ.2]
    have hc := hcurv (Δ + σ) hy0 (by linarith [hσ.2])
    rcases hΔ.eq_or_lt with hΔ0 | hΔ0
    · rw [← hΔ0] at hc ⊢
      simp only [zero_mul, zero_add] at hc ⊢
      linarith
    · have hsl := P1_convexOn.slope_le_of_hasDerivAt
        (show σ ∈ Ico (0 : ℝ) 1 from ⟨hσ.1.le, by linarith [hσ.2]⟩)
        (show Δ + σ ∈ Ico (0 : ℝ) 1 from ⟨hy0.le, hy1⟩) (by linarith) (hasDerivAt_P1 hy0 hy1)
      rw [slope_def_field, show Δ + σ - σ = Δ by ring, div_le_iff₀ hΔ0] at hsl
      linarith
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 s) hcont hderiv hnonneg
  have hG := hmono ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs
  have hP0 : P 0 = 0 := by simp
  simp only [G, mul_zero, add_zero, hP0] at hG
  linarith

/-! ## 4. The diagonal `a = b` -/

theorem gap_le_cost_of_eq {ι : Type*} [Fintype ι] (μ : InteriorLaw ι) (hab : μ.a = μ.b)
    (hactive : phi μ.midpoint μ.meanEntropy ≤ psi μ.midpoint μ.meanEntropy) :
    μ.gap ≤ μ.cost := by
  apply μ.gap_le_of_splitBound hactive
  have hΔ : μ.entropyDrop = 0 := by
    unfold InteriorLaw.entropyDrop InteriorLaw.midpoint
    rw [hab, show (μ.b + μ.b) / 2 = μ.b by ring]
    ring
  have hsplit : μ.splitBound = 0 := by
    unfold InteriorLaw.splitBound
    rw [hΔ, zero_add, sub_self]
  rw [hsplit]
  have h0 : interiorCost μ.a μ.b = 0 := by unfold interiorCost; rw [hab]; ring
  have h1 := μ.interiorCost_le_psiLogSumCostFloor
  have h2 := μ.psiLogSumCostFloor_le_cost
  linarith

end CKLaneM07

#check @CKLaneM07.crR_mono
#check @CKLaneM07.entropyDrop_eq_cr
#check @CKLaneM07.crR_le_poly
#check @CKLaneM07.entropyDrop_le_K
#check @CKLaneM07.etaCurvature_H
#check @CKLaneM07.etaCurvature_le_anchor
#check @CKLaneM07.etaCurvature_H_le
#check @CKLaneM07.derivative_criterion
#check @CKLaneM07.gap_le_cost_of_eq
#print axioms CKLaneM07.crR_mono
#print axioms CKLaneM07.entropyDrop_le_K
#print axioms CKLaneM07.etaCurvature_H_le
#print axioms CKLaneM07.derivative_criterion
#print axioms CKLaneM07.gap_le_cost_of_eq

end


